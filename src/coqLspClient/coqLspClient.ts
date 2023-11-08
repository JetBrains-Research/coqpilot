import { 
    LanguageClient, 
    ServerOptions, 
    LanguageClientOptions, 
    RevealOutputChannelOn
} from "vscode-languageclient/node";

import { 
    WorkspaceConfiguration,
    Uri
} from "vscode";

import logger from "../extension/logger";
import { CoqLspServerConfig } from "./config";
import { StatusBarButton } from "../editor/enableButton";
import { CoqpilotConfigWrapper } from "../extension/config";

export class CoqLspClient extends LanguageClient {
    private statusItem: StatusBarButton;

    constructor(
        statusItem: StatusBarButton, 
        wsConfig: WorkspaceConfiguration, 
        extensionConfig: CoqpilotConfigWrapper,
        path?: Uri
    ) {
        const initializationOptions = CoqLspServerConfig.create();
        let clientOptions: LanguageClientOptions = {
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
                    logger.debug(`Diagnostics received for file ${uri}: ${diagnostics.map((d) => d.message).join(", ")}`);
                }
            }
        };

        if (path) {
            clientOptions = {
                ...clientOptions, 
                workspaceFolder: {
                    uri: path,
                    name: "name",
                    index: 0,
                },
            };
        }

        const extConfig = extensionConfig.config;
        const serverOptions: ServerOptions = {
            command: extConfig.coqLspPath,
            args: wsConfig.args,
        };

        super(
            extConfig.coqLspPath,
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
                this.setFailedStatusBar(emsg);
            });
    }

    override async stop(): Promise<void> {
        super.stop()
            .then(this.updateStatusBar);
    }

    private updateStatusBar = () => {
        this.statusItem.updateClientStatus(this.isRunning());
    };

    private setFailedStatusBar = (emsg: string) => {
        this.statusItem.setFailedStatus(emsg);
    };

    restartLspClient() {
        this.stop().then(() => this.start());
    }
}