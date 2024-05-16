import { MultiroundProfile } from "../../../llm/llmServices/modelParams";
import { UserMultiroundProfile } from "../../../llm/userModelParams";

import { MockLLMModelParams } from "./mockLLMService";

export interface UserModelParamsAddOns {
    modelId?: string;
    choices?: number;
    systemPrompt?: string;
    maxTokensToGenerate?: number;
    tokensLimit?: number;
    multiroundProfile?: UserMultiroundProfile;
}

export interface ModelParamsAddOns {
    modelId?: string;
    choices?: number;
    systemPrompt?: string;
    maxTokensToGenerate?: number;
    tokensLimit?: number;
    multiroundProfile?: MultiroundProfile;
}

export interface MultiroundProfileAddOns {
    maxRoundsNumber?: number;
    defaultProofFixChoices?: number;
    proofFixPrompt?: string;
}

export function enhanceMockParams(
    basicMockParams: MockLLMModelParams,
    multiroundProfile: MultiroundProfileAddOns = {},
    unlimitedTokens: boolean = true
): MockLLMModelParams {
    return {
        ...basicMockParams,
        tokensLimit: unlimitedTokens ? 100000 : basicMockParams.tokensLimit,
        multiroundProfile: {
            ...basicMockParams.multiroundProfile,
            ...multiroundProfile,
        },
    };
}
