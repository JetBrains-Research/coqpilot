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
    abortController?: AbortController
): Promise<CoqLspClient> {
    return createAbstractCoqLspClient(
        CoqLspConfig.createClientConfig(coqLspServerPath),
        logOutputChannel,
        eventLogger,
        abortController
    );
}

export async function createTestCoqLspClient(
    workspaceRootPath?: string
): Promise<CoqLspClient> {
    return createAbstractCoqLspClient(
        CoqLspConfig.createClientConfig(
            process.env.COQ_LSP_PATH || "coq-lsp",
            workspaceRootPath
        )
    );
}

export async function withTestCoqLspClient<T>(
    workspaceRootPath: string | undefined,
    block: (coqLspClient: CoqLspClient) => Promise<T>
) {
    const coqLspClient = await createTestCoqLspClient(workspaceRootPath);
    try {
        return await block(coqLspClient);
    } finally {
        coqLspClient.dispose();
    }
}

export async function withDocumentOpenedByTestCoqLsp<T>(
    documentSpec: DocumentSpec,
    workspaceRootPath: string | undefined,
    block: (
        coqLspClient: CoqLspClient,
        openedDocDiagnostic: DiagnosticMessage
    ) => Promise<T>
): Promise<T> {
    return withTestCoqLspClient(workspaceRootPath, (coqLspClient) =>
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
    abortController?: AbortController
): Promise<CoqLspClient> {
    const coqLspServerConfig = CoqLspConfig.createServerConfig();
    return await CoqLspClientImpl.create(
        coqLspServerConfig,
        coqLspClientConfig,
        logOutputChannel,
        eventLogger,
        abortController
    );
}
