import { OutputChannel, window } from "vscode";

import { CoqLspClient, CoqLspClientInterface } from "./coqLspClient";
import { CoqLspClientConfig, CoqLspConfig } from "./coqLspConfig";

export async function createCoqLspClient(
    coqLspServerPath: string,
    logOutputChannel?: OutputChannel
): Promise<CoqLspClientInterface> {
    return createAbstractCoqLspClient(
        CoqLspConfig.createClientConfig(coqLspServerPath),
        logOutputChannel
    );
}

export async function createTestCoqLspClient(
    workspaceRootPath?: string
): Promise<CoqLspClientInterface> {
    return createAbstractCoqLspClient(
        CoqLspConfig.createClientConfig(
            process.env.COQ_LSP_PATH || "coq-lsp",
            workspaceRootPath
        )
    );
}

async function createAbstractCoqLspClient(
    coqLspClientConfig: CoqLspClientConfig,
    logOutputChannel: OutputChannel = window.createOutputChannel(
        "CoqPilot: coq-lsp events"
    )
): Promise<CoqLspClientInterface> {
    const coqLspServerConfig = CoqLspConfig.createServerConfig();
    return await CoqLspClient.create(
        coqLspServerConfig,
        coqLspClientConfig,
        logOutputChannel
    );
}
