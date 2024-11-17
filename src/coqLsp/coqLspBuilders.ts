import { OutputChannel, window } from "vscode";

import { EventLogger } from "../logging/eventLogger";

import {
    CoqLspClient,
    CoqLspClientImpl,
    DiagnosticMessage,
    DocumentSpec,
} from "./coqLspClient";
import { CoqLspClientConfig, CoqLspConfig } from "./coqLspConfig";

export async function createCoqLspClient(
    coqLspServerPath: string,
    logOutputChannel?: OutputChannel,
    eventLogger?: EventLogger,
    abortSignal?: AbortSignal
): Promise<CoqLspClient> {
    return createAbstractCoqLspClient(
        CoqLspConfig.createClientConfig(coqLspServerPath),
        logOutputChannel,
        eventLogger,
        abortSignal
    );
}

export interface TestCoqLspClientOptions {
    workspaceRootPath?: string;
    abortSignal?: AbortSignal;
}

export async function createTestCoqLspClient(
    options: TestCoqLspClientOptions = {}
): Promise<CoqLspClient> {
    return createAbstractCoqLspClient(
        CoqLspConfig.createClientConfig(
            process.env.COQ_LSP_PATH || "coq-lsp",
            options.workspaceRootPath
        ),
        undefined,
        undefined,
        options.abortSignal
    );
}

export async function withTestCoqLspClient<T>(
    options: TestCoqLspClientOptions,
    block: (coqLspClient: CoqLspClient) => Promise<T>
) {
    const coqLspClient = await createTestCoqLspClient(options);
    try {
        return await block(coqLspClient);
    } finally {
        coqLspClient.dispose();
    }
}

export async function withDocumentOpenedByTestCoqLsp<T>(
    documentSpec: DocumentSpec,
    options: TestCoqLspClientOptions,
    block: (
        coqLspClient: CoqLspClient,
        openedDocDiagnostic: DiagnosticMessage
    ) => Promise<T>
): Promise<T> {
    return withTestCoqLspClient(options, (coqLspClient) =>
        coqLspClient.withTextDocument(documentSpec, (openedDocDiagnostic) =>
            block(coqLspClient, openedDocDiagnostic)
        )
    );
}

async function createAbstractCoqLspClient(
    coqLspClientConfig: CoqLspClientConfig,
    logOutputChannel: OutputChannel = window.createOutputChannel(
        "CoqPilot: coq-lsp events"
    ),
    eventLogger?: EventLogger,
    abortSignal?: AbortSignal
): Promise<CoqLspClient> {
    const coqLspServerConfig = CoqLspConfig.createServerConfig();
    return await CoqLspClientImpl.create(
        coqLspServerConfig,
        coqLspClientConfig,
        logOutputChannel,
        eventLogger,
        abortSignal
    );
}
