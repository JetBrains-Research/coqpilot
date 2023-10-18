import { 
    LanguageClient, 
    ServerOptions, 
    LanguageClientOptions, 
    RevealOutputChannelOn
} from "vscode-languageclient/node";

import { 
    WorkspaceConfiguration,
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

    override async start(): Promise<void> {
        // Something wierd going on here I need an explanation for.
        // Somewhy start() method is called literally all the time,
        // it doesnt make anything bad, as in super.start() it checks
        // if the client is already running, but it's still weird.
        // I tried investigating it, but I couldn't find any reason for it.
        await super.start()
            .then(this.updateStatusBar)
            .catch((error) => {
                let emsg = error.toString();
                logger.info(`Error in coq-lsp start: ${emsg}`);
                this.setFailedStatuBar(emsg);
            });
    }

    override async stop(): Promise<void> {
        super.stop()
            .then(this.updateStatusBar);
    }

    private updateStatusBar = () => {
        this.statusItem.updateClientStatus(this.isRunning());
    };

    private setFailedStatuBar = (emsg: string) => {
        this.statusItem.setFailedStatus(emsg);
    };

    restartLspClient() {
        this.stop().then(() => this.start());
    }
}