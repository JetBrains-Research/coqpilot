import {
    DeepSeekUserModelParams,
    GrazieUserModelParams,
    LMStudioUserModelParams,
    OpenAiUserModelParams,
    PredefinedProofsUserModelParams,
    RangoUserModelParams,
} from "../../llm/userModelParams";

export interface InputModelsParams {
    predefinedProofsModelParams: PredefinedProofsUserModelParams[];
    openAiParams: OpenAiUserModelParams[];
    grazieParams: GrazieUserModelParams[];
    lmStudioParams: LMStudioUserModelParams[];
    deepSeekParams: DeepSeekUserModelParams[];
    rangoParams: RangoUserModelParams[];
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
