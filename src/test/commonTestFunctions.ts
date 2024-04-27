import * as path from "path";
import * as tmp from "tmp";

import { LLMServices } from "../llm/llmServices";
import { GrazieService } from "../llm/llmServices/grazie/grazieService";
import { LMStudioService } from "../llm/llmServices/lmStudio/lmStudioService";
import { OpenAiService } from "../llm/llmServices/openai/openAiService";
import { PredefinedProofsService } from "../llm/llmServices/predefinedProofs/predefinedProofsService";
import {
    PredefinedProofsUserModelParams,
    UserModelsParams,
} from "../llm/userModelParams";

import { CoqLspClient } from "../coqLsp/coqLspClient";
import { CoqLspConfig } from "../coqLsp/coqLspConfig";

import { parseCoqFile } from "../coqParser/parseCoqFile";
import { Theorem } from "../coqParser/parsedTypes";
import { Uri } from "../utils/uri";

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

export function createTrivialModelsParams(
    predefinedProofsModelParams: PredefinedProofsUserModelParams[] = []
): UserModelsParams {
    return {
        openAiParams: [],
        grazieParams: [],
        predefinedProofsModelParams: predefinedProofsModelParams,
        lmStudioParams: [],
    };
}

export function createSinglePredefinedProofsModelsParams(
    predefinedProofs: string[] = [
        "intros.",
        "reflexivity.",
        "auto.",
        "assumption. intros.",
        "left. reflexivity.",
    ]
): UserModelsParams {
    return createTrivialModelsParams([
        createPredefinedProofsModel("predefined-proofs", predefinedProofs),
    ]);
}

export function createPredefinedProofsModel(
    modelName: string = "predefined-proofs",
    predefinedProofs: string[] = [
        "intros.",
        "reflexivity.",
        "auto.",
        "assumption. intros.",
        "left. reflexivity.",
    ]
): PredefinedProofsUserModelParams {
    return {
        modelName: modelName,
        tactics: predefinedProofs,
    };
}

export async function parseTheoremsFromCoqFile(
    resourcePath: string[],
    projectRootPath?: string[]
): Promise<Theorem[]> {
    const filePath = path.join(getResourceFolder(), ...resourcePath);
    const rootDir = path.join(getResourceFolder(), ...(projectRootPath ?? []));

    const fileUri = Uri.fromPath(filePath);
    const client = createCoqLspClient(rootDir);

    await client.openTextDocument(fileUri);
    const document = await parseCoqFile(fileUri, client);
    await client.closeTextDocument(fileUri);

    return document;
}
