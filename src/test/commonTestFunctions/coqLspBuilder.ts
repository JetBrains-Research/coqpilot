import { window } from "vscode";

import { CoqLspClient } from "../../coqLsp/coqLspClient";
import { CoqLspConfig } from "../../coqLsp/coqLspConfig";

export async function createCoqLspClient(
    workspaceRootPath?: string
): Promise<CoqLspClient> {
    const coqLspServerConfig = CoqLspConfig.createServerConfig();
    const coqLspClientConfig = CoqLspConfig.createClientConfig(
        process.env.COQ_LSP_PATH || "coq-lsp",
        workspaceRootPath
    );
    const logOutputChannel = window.createOutputChannel(
        "CoqPilot: coq-lsp events"
    );

    return await CoqLspClient.create(
        coqLspServerConfig,
        coqLspClientConfig,
        logOutputChannel
    );
}