import {
    commands,
    ExtensionContext,
    workspace,
    Disposable,
    TextEditor,
    window,
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
import { CoqpilotConfig } from "./extension/config";
import { Interactor, GenerationStatus } from "./coqLlmInteraction/interactor";
import * as wm from "./editor/windowManager";
import { VsCodeSpinningWheelProgressBar } from "./extension/vscodeProgressBar";
import logger from "./extension/logger";
import { makeAuxfname, getTextBeforePosition } from "./coqLspClient/utils";

export class Coqpilot implements Disposable {

    private readonly disposables: Disposable[] = [];
    private readonly context: ExtensionContext;
    public client: BaseLanguageClient;
    private proofView: ProofViewInterface;
    private statusItem: StatusBarButton;
    private llmPrompt: LLMPrompt | undefined;
    private llm: LLMInterface; 
    private config: CoqpilotConfig;

    private constructor(
        context: ExtensionContext, 
    ) {
        this.excludeAuxFiles();
        this.context = context;

        const config = CoqpilotConfig.create(
            workspace.getConfiguration('coqpilot')
        );
        
        CoqpilotConfig.checkRequirements(config);
        
        this.config = config;
        this.llm = CoqpilotConfig.getLlm(config);

        this.disposables.push(this.statusItem);
        this.disposables.push(this.textEditorChangeHook);

        this.registerCommand("toggle", this.toggleLspClient.bind(this));
        this.registerEditorCommand("init_history", this.initHistory.bind(this));
        this.registerEditorCommand("run_generation", this.runGeneration.bind(this));

        this.context.subscriptions.push(this);
    }

    initialHistoryFetch = async (editor: TextEditor | undefined) => {
        if (!editor) {
            return;
        } else if (editor.document.languageId !== "coq" || !this.config.parseFileOnInit) {
            return;
        }

        logger.info(`Parsing file ${editor.document.fileName}`);
        await this.initHistory(editor);
    };

    textEditorChangeHook = window.onDidChangeActiveTextEditor((editor) => {
        if (!editor) {
            return;
        } else if (editor.document.languageId !== "coq" || !this.config.parseFileOnEditorChange) {
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
        
        this.llmPrompt = new CoqPromptKShot(thrs, this.config.maxNumberOfTokens);
    }

    async initializeClient() {
        this.statusItem = new StatusBarButton();
        const wsConfig = workspace.getConfiguration("coqpilot");
        this.client = new CoqLspClient(this.statusItem, wsConfig);
        this.proofView = new ProofView(this.client, this.statusItem); 

        logger.info("Client prepaired, starting");
        await this.client.start();
    
        this.context.subscriptions.push(this.proofView);
    }

    async runGeneration(editor: TextEditor) {
        if (this.config.openaiApiKey === "None") {
            wm.showApiKeyNotProvidedMessage(); return;
        } else if (editor.document.languageId !== "coq") {
            wm.showIncorrectFileFormatMessage(); return;
        } else if (!this.client.isRunning()) {
            wm.showClientNotRunningMessage(); return;
        }

        const auxFile = makeAuxfname(editor.document.uri);
        const cursorPos = editor.selection.active;
        const textBeforePos = getTextBeforePosition(editor.document.getText(), cursorPos);

        await this.proofView.copyAndOpenFile(textBeforePos, auxFile);

        const auxThr = await this.proofView.getAuxTheoremAtCurPosition(auxFile, 1, cursorPos);
        if (!auxThr) {
            wm.showNoGoalMessage();
            return;
        }

        const [thrStatement, thrName] = auxThr;
        if (!this.llmPrompt) {
            wm.fileSnapshotRequired();
            return;
        }

        const progressBar = new VsCodeSpinningWheelProgressBar();
        const interactor = new Interactor(
            this.llmPrompt, 
            this.llm, 
            progressBar,
            this.config.logAttempts,
            this.config.proofAttemsPerOneTheorem, 
            this.config.logFolderPath
        );
        const proof = await interactor.runProofGeneration(
            thrName,
            thrStatement,
            auxFile,
            this.proofView.checkTheorems.bind(this.proofView)
        );

        switch (proof.status) {
            case GenerationStatus.success:
                wm.showSearchSucessMessage(editor, proof.data);
                break;
            case GenerationStatus.searchFailed:
                wm.showSearchFailureMessage(thrName);
                break; 
            default:
                wm.showExceptionMessage(proof.toString());
                break;
        }

    }

    toggleLspClient() {
        logger.info("Toggle Extension");
        if (this.client?.isRunning()) {
            this.client?.stop();
        } else {
            this.client?.start();
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