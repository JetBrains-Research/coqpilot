import { LLMServices } from "../../llm/llmServices";
import { GrazieService } from "../../llm/llmServices/grazie/grazieService";
import { LMStudioService } from "../../llm/llmServices/lmStudio/lmStudioService";
import {
    ModelsParams,
    PredefinedProofsModelParams,
} from "../../llm/llmServices/modelParams";
import { PredefinedProofsModelParamsResolver } from "../../llm/llmServices/modelParamsResolvers";
import { OpenAiService } from "../../llm/llmServices/openai/openAiService";
import { PredefinedProofsService } from "../../llm/llmServices/predefinedProofs/predefinedProofsService";
import { PredefinedProofsUserModelParams } from "../../llm/userModelParams";

import { resolveOrThrow } from "./resolveOrThrow";

export function createDefaultServices(): LLMServices {
    const predefinedProofsService = new PredefinedProofsService();
    const openAiService = new OpenAiService();
    const grazieService = new GrazieService();
    const lmStudioService = new LMStudioService();
    return {
        predefinedProofsService,
        openAiService,
        grazieService,
        lmStudioService,
    };
}

export function createTrivialModelsParams(
    predefinedProofsModelParams: PredefinedProofsModelParams[] = []
): ModelsParams {
    return {
        predefinedProofsModelParams: predefinedProofsModelParams,
        openAiParams: [],
        grazieParams: [],
        lmStudioParams: [],
    };
}

export function createPredefinedProofsModel(
    modelId: string = "predefined-proofs",
    predefinedProofs: string[] = [
        "intros.",
        "reflexivity.",
        "auto.",
        "assumption. intros.",
        "left. reflexivity.",
    ]
): PredefinedProofsModelParams {
    const inputModelParams: PredefinedProofsUserModelParams = {
        modelId: modelId,
        tactics: predefinedProofs,
    };
    return resolveOrThrow(
        new PredefinedProofsModelParamsResolver(),
        inputModelParams
    );
}

export function createPredefinedProofsModelsParams(
    predefinedProofs: string[] = [
        "intros.",
        "reflexivity.",
        "auto.",
        "assumption. intros.",
        "left. reflexivity.",
    ]
): ModelsParams {
    return createTrivialModelsParams([
        createPredefinedProofsModel("predefined-proofs", predefinedProofs),
    ]);
}
