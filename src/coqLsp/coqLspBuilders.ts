import { CoqLspClient } from "./coqLspClient";
import { CoqLspClientConfig, CoqLspConfig } from "./coqLspConfig";

export function createCoqLspClient(): CoqLspClient {
    return createAbstractCoqLspClient(CoqLspConfig.createClientConfig());
}

export function createTestCoqLspClient(
    workspaceRootPath?: string
): CoqLspClient {
    return createAbstractCoqLspClient(
        CoqLspConfig.createClientConfig(
            process.env.COQ_LSP_PATH || "coq-lsp",
            workspaceRootPath
        )
    );
}

function createAbstractCoqLspClient(
    coqLspClientConfig: CoqLspClientConfig
): CoqLspClient {
    const coqLspServerConfig = CoqLspConfig.createServerConfig();
    return new CoqLspClient(coqLspServerConfig, coqLspClientConfig);
}
