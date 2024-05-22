import { MockLLMModelParams } from "./mockLLMService";
import { MultiroundProfileAddOns } from "./modelParamsAddOns";

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
