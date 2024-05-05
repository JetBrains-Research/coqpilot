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
    predefinedProofsModelParams: PredefinedProofsUserModelParams[] = []
): UserModelsParams {
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
