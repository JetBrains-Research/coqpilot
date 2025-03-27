import {
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
    rangoParams: [],
};
