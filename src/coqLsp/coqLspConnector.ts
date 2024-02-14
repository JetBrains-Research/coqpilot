import { 
    LanguageClientOptions, 
    RevealOutputChannelOn
} from "vscode-languageclient";
import {
    LanguageClient, 
    ServerOptions, 
} from "vscode-languageclient/node";
import { 
    CoqLspServerConfig, 
    CoqLspClientConfig 
} from "./coqLspConfig";
import { EventLogger } from "../logging/eventLogger";

export class CoqLspConnector extends LanguageClient {
    constructor(
        serverConfig: CoqLspServerConfig,
        clientConfig: CoqLspClientConfig,
        private eventLogger?: EventLogger
    ) {
        let clientOptions: LanguageClientOptions = {
            documentSelector: [
                { scheme: "file", language: "coq" },
                { scheme: "file", language: "markdown", pattern: "**/*.mv" },
            ],
            outputChannelName: "Coqpilot: coq-lsp events",
            revealOutputChannelOn: RevealOutputChannelOn.Info,
            initializationOptions: serverConfig,
            markdown: { isTrusted: true, supportHtml: true },
            middleware: {
                handleDiagnostics: (_uri, _diagnostics, _next) => {
                    return;
                },
                provideDocumentSymbols: (_document, _token, _next) => {
                    return [];
                }
            }
        };

        const serverOptions: ServerOptions = {
            command: clientConfig.coq_lsp_server_path
        };

        super(
            clientConfig.coq_lsp_server_path,
            "Coq LSP Server",
            serverOptions,
            clientOptions
        );
    }

    override async start(): Promise<void> {
        await super.start()
            .then(this.logStatusUpdate.bind(this, 'started'))
            .catch((error) => {
                let emsg = error.toString();
                this.eventLogger?.log('coq-lsp-start-error', emsg);
                this.logStatusUpdate('stopped');
            });
    }

    override async stop(): Promise<void> {
        super.stop()
            .then(this.logStatusUpdate.bind(this, 'stopped'));
    }


    private logStatusUpdate = (status: "started" | "stopped") => {
        this.eventLogger?.log('coq-lsp-status-change', status);
    };

    restartLspClient() {
        this.stop().then(() => this.start());
    }
}