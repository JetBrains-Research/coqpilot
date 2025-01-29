import { OutputChannel, Uri } from "vscode";
import {
    LanguageClientOptions,
    RevealOutputChannelOn,
    Trace,
} from "vscode-languageclient";
import { LanguageClient, ServerOptions } from "vscode-languageclient/node";

import { EventLogger } from "../logging/eventLogger";
import { getErrorMessage } from "../utils/errorsUtils";

import { CoqLspClientConfig, CoqLspServerConfig } from "./coqLspConfig";

export class CoqLspConnector extends LanguageClient {
    static wrongServerSuspectedEvent = "wrong-lsp-server-suspected";

    constructor(
        serverConfig: CoqLspServerConfig,
        clientConfig: CoqLspClientConfig,
        public logOutputChannel: OutputChannel,
        private eventLogger?: EventLogger
    ) {
        let clientOptions: LanguageClientOptions = {
            documentSelector: [
                { scheme: "file", language: "coq" },
                { scheme: "file", language: "markdown", pattern: "**/*.mv" },
            ],
            outputChannel: logOutputChannel,
            revealOutputChannelOn: RevealOutputChannelOn.Info,
            initializationOptions: serverConfig,
            markdown: { isTrusted: true, supportHtml: true },
            middleware: {
                handleDiagnostics: (_uri, _diagnostics, _next) => {
                    return;
                },
                provideDocumentSymbols: (_document, _token, _next) => {
                    return [];
                },
            },
        };

        if (clientConfig.workspace_root_path) {
            clientOptions = {
                ...clientOptions,
                workspaceFolder: {
                    uri: Uri.file(clientConfig.workspace_root_path),
                    name: "name",
                    index: 0,
                },
            };
        }

        const serverOptions: ServerOptions = {
            command: clientConfig.coq_lsp_server_path,
        };

        super(
            clientConfig.coq_lsp_server_path,
            "Coq LSP Server",
            serverOptions,
            clientOptions
        );
    }

    override async start(): Promise<void> {
        super.setTrace(Trace.Verbose);
        await super
            .start()
            .then()
            .catch((e) => {
                this.eventLogger?.log(
                    "coq-lsp-start-error",
                    getErrorMessage(e)
                );
                throw e;
            });
    }

    private isVersioningError(message: string): boolean {
        return message.includes("Incorrect client version");
    }

    override error(message: string, data: any, showNotification = true) {
        if (this.isVersioningError(message)) {
            this.eventLogger?.log(
                CoqLspConnector.wrongServerSuspectedEvent,
                message
            );
        } else {
            this.eventLogger?.log("coq-lsp-error", message);
        }
        super.error(message, data, showNotification);
    }
}
