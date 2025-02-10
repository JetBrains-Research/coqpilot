import { LLMServices } from "../../llm/llmServices";
import { DeepSeekService } from "../../llm/llmServices/deepSeek/deepSeekService";
import { GrazieService } from "../../llm/llmServices/grazie/grazieService";
import { LMStudioService } from "../../llm/llmServices/lmStudio/lmStudioService";
import {
    ModelsParams,
    PredefinedProofsModelParams,
} from "../../llm/llmServices/modelParams";
import { OpenAiService } from "../../llm/llmServices/openai/openAiService";
import { PredefinedProofsModelParamsResolver } from "../../llm/llmServices/predefinedProofs/predefinedProofsModelParamsResolver";
import { PredefinedProofsService } from "../../llm/llmServices/predefinedProofs/predefinedProofsService";
import { resolveOrThrow } from "../../llm/llmServices/utils/resolveOrThrow";
import { PredefinedProofsUserModelParams } from "../../llm/userModelParams";

export function createDefaultServices(): LLMServices {
    const predefinedProofsService = new PredefinedProofsService();
    const openAiService = new OpenAiService();
    const grazieService = new GrazieService();
    const lmStudioService = new LMStudioService();
    const deepSeekService = new DeepSeekService();
    return {
        predefinedProofsService,
        openAiService,
        grazieService,
        lmStudioService,
        deepSeekService,
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
        deepSeekParams: [],
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
