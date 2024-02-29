import * as path from "path";
import { CoqLspClient } from "../coqLsp/coqLspClient";
import { CoqLspConfig } from "../coqLsp/coqLspConfig";

export function getResourceFolder() {
    const dirname = path.dirname(path.dirname(__dirname));
    return path.join(dirname, "src", "test", "resources");
}

export function createCoqLspClient(workspaceRootPath?: string): CoqLspClient {
    const coqLspServerConfig = CoqLspConfig.createServerConfig();
    const coqLspClientConfig = CoqLspConfig.createClientConfig(
        process.env.COQ_LSP_PATH || "coq-lsp",
        workspaceRootPath
    );

    return new CoqLspClient(coqLspServerConfig, coqLspClientConfig);
}
