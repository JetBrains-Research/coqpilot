import { OutputChannel, window } from "vscode";

import { EventLogger } from "../logging/eventLogger";

import { CoqLspClient, CoqLspClientImpl } from "./coqLspClient";
import { CoqLspClientConfig, CoqLspConfig } from "./coqLspConfig";

export async function createCoqLspClient(
    coqLspServerPath: string,
    logOutputChannel?: OutputChannel,
    eventLogger?: EventLogger
): Promise<CoqLspClient> {
    return createAbstractCoqLspClient(
        CoqLspConfig.createClientConfig(coqLspServerPath),
        logOutputChannel,
        eventLogger
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

async function createAbstractCoqLspClient(
    coqLspClientConfig: CoqLspClientConfig,
    logOutputChannel: OutputChannel = window.createOutputChannel(
        "CoqPilot: coq-lsp events"
    ),
    eventLogger?: EventLogger
): Promise<CoqLspClient> {
    const coqLspServerConfig = CoqLspConfig.createServerConfig();
    return await CoqLspClientImpl.create(
        coqLspServerConfig,
        coqLspClientConfig,
        logOutputChannel,
        eventLogger
    );
}
