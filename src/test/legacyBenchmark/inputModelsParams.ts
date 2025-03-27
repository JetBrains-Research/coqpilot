import {
    DeepSeekUserModelParams,
    GrazieUserModelParams,
    LMStudioUserModelParams,
    MockRangoUserModelParams,
    OpenAiUserModelParams,
    PredefinedProofsUserModelParams,
} from "../../llm/userModelParams";

export interface InputModelsParams {
    predefinedProofsModelParams: PredefinedProofsUserModelParams[];
    openAiParams: OpenAiUserModelParams[];
    grazieParams: GrazieUserModelParams[];
    lmStudioParams: LMStudioUserModelParams[];
    deepSeekParams: DeepSeekUserModelParams[];
    rangoParams: MockRangoUserModelParams[];
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
    rangoParams: [],
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
    rangoParams: [],
};
