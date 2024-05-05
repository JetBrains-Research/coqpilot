import { LLMServices } from "../../llm/llmServices";
import { GrazieService } from "../../llm/llmServices/grazie/grazieService";
import { LMStudioService } from "../../llm/llmServices/lmStudio/lmStudioService";
import { OpenAiService } from "../../llm/llmServices/openai/openAiService";
import { PredefinedProofsService } from "../../llm/llmServices/predefinedProofs/predefinedProofsService";
import {
    PredefinedProofsUserModelParams,
    UserModelsParams,
} from "../../llm/userModelParams";

export function createDefaultServices(): LLMServices {
    const openAiService = new OpenAiService();
    const grazieService = new GrazieService();
    const predefinedProofsService = new PredefinedProofsService();
    const lmStudioService = new LMStudioService();
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

export function createPredefinedProofsModel(
    modelId: string = "predefined-proofs",
    predefinedProofs: string[] = [
        "intros.",
        "reflexivity.",
        "auto.",
        "assumption. intros.",
        "left. reflexivity.",
    ]
): PredefinedProofsUserModelParams {
    return {
        modelId: modelId,
        tactics: predefinedProofs,
    };
}

export function createPredefinedProofsModelsParams(
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
