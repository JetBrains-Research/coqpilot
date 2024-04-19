import * as path from "path";
import * as tmp from "tmp";

import { LLMServices } from "../llm/llmServices";
import { GrazieService } from "../llm/llmServices/grazie/grazieService";
import { LMStudioService } from "../llm/llmServices/lmStudio/lmStudioService";
import { OpenAiService } from "../llm/llmServices/openai/openAiService";
import { PredefinedProofsService } from "../llm/llmServices/predefinedProofs/predefinedProofsService";

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

export function createDefaultServices(): LLMServices {
    const openAiService = new OpenAiService(tmp.fileSync().name);
    const grazieService = new GrazieService(tmp.fileSync().name);
    const predefinedProofsService = new PredefinedProofsService(
        tmp.fileSync().name
    );
    const lmStudioService = new LMStudioService(tmp.fileSync().name);
    return {
        openAiService,
        grazieService,
        predefinedProofsService,
        lmStudioService,
    };
}
