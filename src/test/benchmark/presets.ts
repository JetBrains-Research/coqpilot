import { UserModelsParams } from "../../llm/userModelParams";

export const onlyAutoModelsParams: UserModelsParams = {
    openAiParams: [],
    grazieParams: [],
    predefinedProofsModelParams: [
        {
            modelName: "Predefined `auto`",
            choices: undefined,

            systemPrompt: undefined,

            newMessageMaxTokens: undefined,
            tokensLimit: undefined,

            multiroundProfile: undefined,
            tactics: ["auto."],
        },
    ],
    lmStudioParams: [],
};
