import { MultiroundProfile } from "../../../proofProviders/impl/modelParams";

import { MockServiceModelParams } from "./mockService";

export function enhanceMockParams(
    basicMockParams: MockServiceModelParams,
    multiroundProfile: Partial<MultiroundProfile> = {},
    unlimitedTokens: boolean = true
): MockServiceModelParams {
    return {
        ...basicMockParams,
        tokensLimit: unlimitedTokens ? 100000 : basicMockParams.tokensLimit,
        multiroundProfile: {
            ...basicMockParams.multiroundProfile,
            ...multiroundProfile,
        },
    };
}
