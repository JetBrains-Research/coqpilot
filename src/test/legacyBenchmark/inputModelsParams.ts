import {
    DeepSeekUserModelParams,
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
    deepSeekParams: DeepSeekUserModelParams[];
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
    deepSeekParams: [],
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
    deepSeekParams: [],
};
