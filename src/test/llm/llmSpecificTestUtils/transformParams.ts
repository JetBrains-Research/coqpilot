import { MultiroundProfile } from "../../../llm/llmServices/modelParams";

import { MockLLMModelParams } from "./mockLLMService";

export function enhanceMockParams(
    basicMockParams: MockLLMModelParams,
    multiroundProfile: Partial<MultiroundProfile> = {},
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
