import {
    commands,
    ExtensionContext,
    workspace,
    Disposable,
    TextEditor,
    window,
    Position,
} from "vscode";

import {
    BaseLanguageClient,
} from "vscode-languageclient";

import { CoqLspClient } from "./coqLspClient/coqLspClient";
import { ProofView, ProofViewInterface } from "./coqLspClient/proofView";
import { StatusBarButton } from "./editor/enableButton";
import { LLMPrompt } from "./coqLlmInteraction/llmPromptInterface";
import { CoqPromptKShot } from "./coqLlmInteraction/coqLlmPrompt";
import { LLMInterface } from "./coqLlmInteraction/llmInterface";
import { CoqpilotConfig, CoqpilotConfigWrapper } from "./extension/config";
import { 
    Interactor, 
    GenerationStatus, 
    GenerationResult, 
} from "./coqLlmInteraction/interactor";
import * as wm from "./editor/windowManager";
import { VsCodeSpinningWheelProgressBar } from "./extension/vscodeProgressBar";
import logger from "./extension/logger";
import { makeAuxfname } from "./coqLspClient/utils";
import * as lspUtils from "./coqLspClient/utils";
import { ProofStep } from "./lib/pvTypes";
import * as utils from "./coqLspClient/utils";
import { shuffleArray } from "./coqLlmInteraction/utils";

export class Coqpilot implements Disposable {

    private readonly disposables: Disposable[] = [];
    private readonly context: ExtensionContext;
    public client: BaseLanguageClient;
    private proofView: ProofViewInterface;
    private statusItem: StatusBarButton;
    private llmPrompt: LLMPrompt | undefined;
    private llm: LLMInterface; 
    private config: CoqpilotConfigWrapper = CoqpilotConfig.getNew();

    private constructor(
        context: ExtensionContext, 
    ) {
        this.excludeAuxFiles();
        this.context = context;

        this.llm = CoqpilotConfig.getLlm(this.config);

        this.disposables.push(this.statusItem);
        this.disposables.push(this.textEditorChangeHook);

        this.registerCommand("toggle", this.toggleLspClient.bind(this));
        this.registerEditorCommand("init_history", this.initHistory.bind(this));
        this.registerEditorCommand("run_generation", this.runGeneration.bind(this));
        this.registerEditorCommand("prove_all_holes", this.runProveAllAdmitted.bind(this));
        this.registerEditorCommand("prove_in_selection", this.runProveAdmittedInSelection.bind(this));

        this.context.subscriptions.push(this);
    }

    initialHistoryFetch = async (editor: TextEditor | undefined) => {
        if (!editor) {
            return;
        } else if (editor.document.languageId !== "coq" || !this.config.config.parseFileOnInit) {
            return;
        }

        logger.info(`Parsing file ${editor.document.fileName}`);
        await this.initHistory(editor);
    };

    textEditorChangeHook = window.onDidChangeActiveTextEditor((editor) => {
        if (!editor) {
            return;
        } else if (editor.document.languageId !== "coq" || !this.config.config.parseFileOnEditorChange) {
            return;
        }        

        logger.info(`Parsing file ${editor.document.fileName}`);
        this.initHistory(editor);
    });

    private registerCommand(command: string, fn: () => void) {
        let disposable = commands.registerCommand("coqpilot." + command, fn);
        this.context.subscriptions.push(disposable);
    }

    private registerEditorCommand(command: string, fn: (editor: TextEditor) => void) {
        let disposable = commands.registerTextEditorCommand(
            "coqpilot." + command,
            fn
        );
        this.context.subscriptions.push(disposable);
    }

    static async init(
        context: ExtensionContext
    ): Promise<Coqpilot> {
        const coqpilot = new Coqpilot(context);
        await coqpilot.initializeClient();
        await coqpilot.initialHistoryFetch(window.activeTextEditor);
        await wm.addAuxFilesToGitIgnore();

        return coqpilot;
    }

    async initHistory(editor: TextEditor) {
        logger.info("Start initializing history");
        if (!this.client.isRunning()) {
            wm.showClientNotRunningMessage(); return;
        } else if (editor.document.languageId !== "coq") {
            wm.showIncorrectFileFormatMessage(); return;
        }

        logger.info("Conditions satisfied, start parsing file");

        const thrs = await this.proofView.parseFile(editor);
        if (!thrs) {
            logger.info("No theorems in file");
            throw new Error("Error parsing file");
        }

        logger.info(`Theorems retrieved:\n${thrs}`);
        
        this.llmPrompt = new CoqPromptKShot(thrs, this.config.config.maxNumberOfTokens);

        logger.info(`Initialized with theorems: ${this.llmPrompt.trainingTheorems.map((thr) => thr.name)}`);
        logger.info(this.llmPrompt.trainingTheorems.map((thr) => thr.toString()));
    }

    async initializeClient() {
        this.statusItem = new StatusBarButton();
        const wsConfig = workspace.getConfiguration("coqpilot");
        this.client = new CoqLspClient(this.statusItem, wsConfig, this.config);
        this.proofView = new ProofView(this.client, this.statusItem); 

        logger.info("Client prepaired, starting");
        await this.client.start();
    
        this.context.subscriptions.push(this.proofView);
        this.context.subscriptions.push(this.client);
    }

    private checkConditions(editor: TextEditor) {
        if (this.config.config.useGpt && this.config.config.openaiApiKey === "None") {
            wm.showApiKeyNotProvidedMessage(); return false;
        } else if (editor.document.languageId !== "coq") {
            wm.showIncorrectFileFormatMessage(); return false;
        } else if (!this.client.isRunning()) {
            wm.showClientNotRunningMessage(); return false;
        }

        return true;
    }

    private async generateAtPoint(
        editor: TextEditor, 
        position: Position
    ): Promise<GenerationResult<string>> {
        if (!this.checkConditions(editor)) {
            return GenerationResult.editorError();
        }

        const auxFile = makeAuxfname(editor.document.uri);
        const auxThr = await this.proofView.getAuxTheoremAtCurPosition(
            auxFile, editor.document.getText(), position
        );

        if (!auxThr) {
            wm.showNoGoalMessage();
            return GenerationResult.editorError();
        }

        const [thrStatement, thrName] = auxThr;
        if (!this.llmPrompt) {
            wm.fileSnapshotRequired();
            return GenerationResult.editorError();
        }

        const progressBar = new VsCodeSpinningWheelProgressBar();
        const interactor = new Interactor(
            this.llmPrompt, 
            this.llm, 
            progressBar,
            this.config.config.logAttempts,
            this.config.config.proofAttemsPerOneTheorem, 
            this.config.config.logFolderPath
        );
        const proof = await interactor.runProofGeneration(
            thrName,
            thrStatement,
            auxFile,
            this.proofView.checkTheorems.bind(this.proofView)
        );

        return proof;
    }

    async runGeneration(editor: TextEditor) {
        const proof = await this.generateAtPoint(editor, editor.selection.active);
        switch (proof.status) {
            case GenerationStatus.success:
                wm.showSearchSucessMessage(editor, proof.data, editor.selection.active);
                break;
            case GenerationStatus.searchFailed:
                wm.showSearchFailureMessageHole(editor.selection.active);
                break; 
            default:
                wm.showExceptionMessage(proof.toString());
                break;
        }
    }

    async proveHoles(editor: TextEditor, holes: ProofStep[]) {
        if (this.config.config.shuffleHoles) {
            shuffleArray(holes);
        }
        
        for (const hole of holes) {
            // Run proof generation at the start of the hole
            const position = lspUtils.toVPosition(hole.range.start);
            const proof = await this.generateAtPoint(editor, position);
            switch (proof.status) {
                case GenerationStatus.success:
                    // Remove the text of the hole from the editor
                    const range = lspUtils.toVRange(hole.range);
                    await editor.edit((editBuilder) => {
                        editBuilder.delete(range);
                    });

                    const inlinedProof = proof.data.replace(/\n/g, " ");
                    wm.showSearchSucessMessage(editor, inlinedProof, position);
                    break;
                case GenerationStatus.searchFailed:
                    wm.showSearchFailureMessageHole(position);
                    break; 
                default:
                    wm.showExceptionMessage(proof.toString());
                    break;
            }
        }
    }

    async runProveAllAdmitted(editor: TextEditor) {
        await this.initHistory(editor);
        const allTheorems = this.llmPrompt?.theoremsFromFile;
        console.log(allTheorems);
        const proofHoles = allTheorems.map((thr) => thr.proof.holes).flat();
        await this.proveHoles(editor, proofHoles);
    }

    async runProveAdmittedInSelection(editor: TextEditor) {
        await this.initHistory(editor);
        const allTheorems = this.llmPrompt?.theoremsFromFile;
        const proofHoles = allTheorems
            .map((thr) => thr.proof.holes)
            .flat()
            .filter((hole) => editor.selection.contains(
                utils.toVPosition(hole.range.start)
            ));
        await this.proveHoles(editor, proofHoles);
    }

    async toggleLspClient() {
        logger.info("Toggle Extension");
        if (this.client?.isRunning()) {
            this.client?.dispose(2000)
                .then(() => this.proofView?.dispose());
        } else {
            await this.initializeClient();
        }
    }

    excludeAuxFiles() {
        // Hide files generated to check proofs
        let activationConfig = workspace.getConfiguration();
        let fexc: any = activationConfig.get("files.exclude");
        activationConfig.update("files.exclude", {
            // eslint-disable-next-line @typescript-eslint/naming-convention
            '**/*_cp_aux.v': true,
            ...fexc,
        });
    }

    dispose() {
        wm.cleanAuxFiles();
        this.client?.stop();
        this.disposables.forEach((d) => d.dispose());
    }   
}