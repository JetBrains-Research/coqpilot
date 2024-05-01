import { UserMultiroundProfile } from "../../../llm/userModelParams";

import { MockLLMModelParams } from "./mockLLMService";

export function enhanceMockParams(
    basicMockParams: MockLLMModelParams,
    multiroundProfile: UserMultiroundProfile = {},
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
