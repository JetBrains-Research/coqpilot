import {
    GrazieUserModelParams,
    LMStudioUserModelParams,
    OpenAiUserModelParams,
    PredefinedProofsUserModelParams,
} from "../../llm/userModelParams";

export interface InputModelsParams {
    predefinedProofsModelParams: PredefinedProofsUserModelParams[];
    openAiParams: OpenAiUserModelParams[];
    grazieParams: GrazieUserModelParams[];
    lmStudioParams: LMStudioUserModelParams[];
}

export const onlyAutoModelsParams: InputModelsParams = {
    openAiParams: [],
    grazieParams: [],
    predefinedProofsModelParams: [
        {
            modelId: "Predefined tactic",
            tactics: ["firstorder auto with *."],
        },
    ],
    lmStudioParams: [],
};

export const tacticianModelsParams: InputModelsParams = {
    openAiParams: [],
    grazieParams: [],
    predefinedProofsModelParams: [
        {
            modelId: "Tactician",
            tactics: ["synth."],
        },
    ],
    lmStudioParams: [],
};
