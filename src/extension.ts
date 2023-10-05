import {
    commands,
    ExtensionContext,
    workspace,
    WorkspaceConfiguration,
    Disposable,
    TextEditor
} from "vscode";

import {
    BaseLanguageClient,
    LanguageClientOptions,
    RevealOutputChannelOn
} from "vscode-languageclient";

import { CoqLspServerConfig } from "./coqLspClient/config";
import { ProofView } from "./coqLspClient/proofView";
import { StatusBarButton } from "./editor/enableButton";
import { LLMPrompt } from "./coqLlmInteraction/llmPromptInterface";
import { CoqPromptKShot } from "./coqLlmInteraction/coqLlmPrompt";
import { LLMInterface } from "./coqLlmInteraction/llmInterface";
import { CoqpilotConfig } from "./extension/config";
import { Interactor } from "./coqLlmInteraction/interactor";
import * as wm from "./editor/windowManager";
import { VsCodeSpinningWheelProgressBar } from "./extension/vscodeProgressBar";

export type ClientFactoryType = (
    context: ExtensionContext,
    clientOptions: LanguageClientOptions,
    wsConfig: WorkspaceConfiguration
) => BaseLanguageClient;

export class Coqpilot implements Disposable {

    private readonly disposables: Disposable[] = [];
    private readonly context: ExtensionContext;
    public client: BaseLanguageClient;
    private proofView: ProofView;
    private statusItem: StatusBarButton;
    private clientFactory: ClientFactoryType;
    private llmPrompt: LLMPrompt | undefined;
    private llm: LLMInterface; 
    private config: CoqpilotConfig;

    private constructor(context: ExtensionContext, clientFactory: ClientFactoryType) {
        this.excludeAuxFiles();

        this.context = context;
        this.clientFactory = clientFactory;

        const config = CoqpilotConfig.create(
            workspace.getConfiguration('coqpilot')
        );
        
        CoqpilotConfig.checkRequirements(config);
        
        this.config = config;
        this.llm = CoqpilotConfig.getLlm(config);

        this.disposables.push(this.statusItem);

        this.registerCommand("coq-lsp.toggle", this.toggleLspClient);
        this.registerCommand("coq-lsp.restart", this.restartLspClient);
        this.registerCommand("coq-lsp.stop", this.stopLspClient);

        this.registerEditorCommand("init_history", this.initHistory.bind(this));
        this.registerEditorCommand("run_generation", this.runGeneration.bind(this));
    }

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

    static async init(context: ExtensionContext, clientFactory: ClientFactoryType): Promise<Coqpilot> {
        const coqpilot = new Coqpilot(context, clientFactory);
        await coqpilot.activateCoqLSP();

        return coqpilot;
    }

    async initHistory(editor: TextEditor) {
        const thrs = await this.proofView.parseFile(editor);
        if (!thrs) {
            console.log("No theorems in file");
            throw new Error("Error parsing file");
            return;
        }
        
        this.llmPrompt = new CoqPromptKShot(thrs, this.config.maxNumberOfTokens);
    }

    async activateCoqLSP() {
        if (this.client?.isRunning()) { 
            return;
        }
    
        const wsConfig = workspace.getConfiguration("coqpilot");
        const initializationOptions = CoqLspServerConfig.create();

        const clientOptions: LanguageClientOptions = {
            documentSelector: [
                { scheme: "file", language: "coq" },
                { scheme: "file", language: "markdown", pattern: "**/*.mv" },
            ],
            outputChannelName: "Coqpilot: coq-lsp events",
            revealOutputChannelOn: RevealOutputChannelOn.Info,
            initializationOptions,
            markdown: { isTrusted: true, supportHtml: true },
        };

        let cP = new Promise<BaseLanguageClient>((resolve) => {
            this.client = this.clientFactory(this.context, clientOptions, wsConfig);
            this.statusItem = new StatusBarButton();
            this.proofView = new ProofView(this.client, this.statusItem);
            resolve(this.client);
        });

        await cP.then((client) =>
            client
                .start()
                .then(this.updateStatusBar)
        ).catch((error) => {
            let emsg = error.toString();
            console.log(`Error in coq-lsp start: ${emsg}`);
            this.setFailedStatuBar(emsg);
        });
    
        this.context.subscriptions.push(this.proofView);
    }

    async runGeneration(editor: TextEditor) {
        if (this.config.openaiApiKey === "None") {
            wm.showApiKeyNotProvidedMessage(); return;
        }

        const auxFile = this.proofView.makeAuxfname(editor.document.uri);
        const cursorPos = editor.selection.active;

        await this.proofView.copyAndOpenFile(editor.document.getText(), auxFile, cursorPos);

        const [thrStatement, thrName] = await this.proofView.getAuxTheoremAtCurPosition(auxFile, 1, cursorPos);
        if (!thrStatement) {
            wm.showNoGoalMessage();
            return;
        }

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

        if (!proof) {
            wm.showSearchFailureMessage(thrName);
            return;
        }

        wm.showSearchSucessMessage(editor, proof);
    }

    private updateStatusBar = () => {
        this.statusItem.updateClientStatus(this.client && this.client.isRunning());
    };

    private setFailedStatuBar = (emsg: string) => {
        this.statusItem.setFailedStatus(emsg);
    };

    private stopLspClient() {
        if (this.client && this.client.isRunning()) {
            this.client
                .dispose(2000)
                .then(this.updateStatusBar)
                .then(() => {
                    this.proofView.dispose();
                });
        }
    }

    private toggleLspClient() {
        if (this.client && this.client.isRunning()) {
            this.stopLspClient();
        } else {
            this.activateCoqLSP();
        }
    }

    private restartLspClient() {
        this.stopLspClient();
        this.activateCoqLSP();
    }

    deactivateCoqLSP(): Thenable<void> | undefined {
        if (!this.client) {
            return undefined;
        }
        return this.client.stop();
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
        this.disposables.forEach((d) => d.dispose());
    }   
}