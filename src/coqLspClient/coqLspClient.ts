import { 
    LanguageClient, 
    ServerOptions, 
    LanguageClientOptions, 
    // BaseLanguageClient,
    RevealOutputChannelOn
} from "vscode-languageclient/node";

import { 
    // ExtensionContext, 
    WorkspaceConfiguration,
    // workspace 
} from "vscode";

import logger from "../extension/logger";
import { CoqLspServerConfig } from "./config";
import { StatusBarButton } from "../editor/enableButton";

export class CoqLspClient extends LanguageClient {
    private statusItem: StatusBarButton;

    constructor(statusItem: StatusBarButton, wsConfig: WorkspaceConfiguration) {
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
            middleware: {
                handleDiagnostics: (uri, diagnostics, _next) => {
                    logger.info(`Diagnostics received for file ${uri}: ${diagnostics.map((d) => d.message).join(", ")}`);
                }
            }
        };

        const serverOptions: ServerOptions = {
            command: "coq-lsp",
            args: wsConfig.args,
        };

        super(
            "coq-lsp",
            "Coq LSP Server",
            serverOptions,
            clientOptions
        );

        this.statusItem = statusItem;
    }

    // async activateCoqLSP() {
    //     logger.info("Start Client");
    //     if (this.isRunning()) { 
    //         return;
    //     }
    
        // const wsConfig = workspace.getConfiguration("coqpilot");
        // const initializationOptions = CoqLspServerConfig.create();

        // const clientOptions: LanguageClientOptions = {
        //     documentSelector: [
        //         { scheme: "file", language: "coq" },
        //         { scheme: "file", language: "markdown", pattern: "**/*.mv" },
        //     ],
        //     outputChannelName: "Coqpilot: coq-lsp events",
        //     revealOutputChannelOn: RevealOutputChannelOn.Info,
        //     initializationOptions,
        //     markdown: { isTrusted: true, supportHtml: true },
        //     middleware: {
        //         handleDiagnostics: (uri, diagnostics, _next) => {
        //             logger.info(`Diagnostics received for file ${uri}: ${diagnostics.map((d) => d.message).join(", ")}`);
        //         }
        //     }
        // };

        // let cP = new Promise<BaseLanguageClient>((resolve) => {
        //     this.client = cf(clientOptions, wsConfig);
        //     resolve(this.client);
        // });

        // await cP.then((client) =>
        //     client
        //         .start()
        //         .then(this.updateStatusBar)
        // ).catch((error) => {
        //     let emsg = error.toString();
        //     logger.info(`Error in coq-lsp start: ${emsg}`);
        //     this.setFailedStatuBar(emsg);
        // });
    // }

    override async start(): Promise<void> {
        await super.start()
            .then(this.updateStatusBar)
            .catch((error) => {
                let emsg = error.toString();
                logger.info(`Error in coq-lsp start: ${emsg}`);
                this.setFailedStatuBar(emsg);
            });
    }

    override async stop(): Promise<void> {
        logger.info("Stop Client");
        this.stop()
            .then(this.updateStatusBar);
    }

    private updateStatusBar = () => {
        this.statusItem.updateClientStatus(this.isRunning());
    };

    private setFailedStatuBar = (emsg: string) => {
        this.statusItem.setFailedStatus(emsg);
    };

    toggleLspClient() {
        logger.info("Toggle Extension");
        if (this.isRunning()) {
            this.stop();
        } else {
            this.start();
        }
    }

    restartLspClient() {
        this.stop().then(() => this.start());
    }

    // deactivateCoqLSP(): Thenable<void> | undefined {
    //     if (!this.client) {
    //         return undefined;
    //     }
    //     return this.client.stop();
    // }
}