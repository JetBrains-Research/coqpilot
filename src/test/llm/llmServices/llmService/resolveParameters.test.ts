import { expect } from "earl";

import { ModelParams } from "../../../../llm/llmServices/modelParams";
import {
    defaultMultiroundProfile,
    defaultTokensLimits,
    resolveParametersWithDefaultsImpl,
} from "../../../../llm/llmServices/utils/defaultParametersResolver";
import { UserModelParams } from "../../../../llm/userModelParams";

import { gptTurboModel } from "../../llmSpecificTestUtils/constants";
import {
    MockLLMModelParams,
    MockLLMService,
    MockLLMUserModelParams,
} from "../../llmSpecificTestUtils/mockLLMService";

suite("[LLMService] Test UserModelParams to ModelParams resolution", () => {
    test("Test resolve with defaults: basic", () => {
        const unresolvedUserParams: UserModelParams = {
            modelName: gptTurboModel,
            systemPrompt: "Generate gorgeous Coq proofs!",
            newMessageMaxTokens: 100,
        };
        const expectedResolvedParams = {
            ...unresolvedUserParams,
            tokensLimit: defaultTokensLimits[unresolvedUserParams.modelName]!,
            multiroundProfile: defaultMultiroundProfile,
        } as ModelParams;

        const actualResolvedParams =
            resolveParametersWithDefaultsImpl(unresolvedUserParams);
        expect(actualResolvedParams).toEqual(expectedResolvedParams);
    });

    test("Test resolve with defaults: partial MultiroundProfile", () => {
        const unresolvedUserParams: UserModelParams = {
            modelName: gptTurboModel,
            systemPrompt: "Generate gorgeous Coq proofs!",
            newMessageMaxTokens: 100,
            tokensLimit: 1000,
            multiroundProfile: {
                maxRoundsNumber: 1,
            },
        };
        const expectedResolvedParams = {
            ...unresolvedUserParams,
            multiroundProfile: {
                ...unresolvedUserParams.multiroundProfile,
                proofFixChoices: defaultMultiroundProfile.proofFixChoices,
                proofFixPrompt: defaultMultiroundProfile.proofFixPrompt,
            },
        } as ModelParams;

        const actualResolvedParams =
            resolveParametersWithDefaultsImpl(unresolvedUserParams);
        expect(actualResolvedParams).toEqual(expectedResolvedParams);
    });

    test("Test resolve with defaults: could not be resolved", () => {
        const unresolvedUserParams: UserModelParams = {
            modelName: "some unknown model",
        };
        // there are no default values for token-related properties for unknown model
        expect(() =>
            resolveParametersWithDefaultsImpl(unresolvedUserParams)
        ).toThrow();
    });

    test("Test resolution by LLMService", () => {
        const mockService = new MockLLMService();
        try {
            const unresolvedMockUserParams: MockLLMUserModelParams = {
                modelName: "mock model",
                systemPrompt: "This system prompt will be overriden by service",
                newMessageMaxTokens: 100,
                tokensLimit: 1000,
                proofsToGenerate: ["auto.", "avto."],
            };
            /*
             * MockLLMService always:
             * - overrides `systemPrompt;
             * - adds `resolvedWithMockLLMService`;
             * - resolves undefined `workerId` to 0.
             * Everything else should be resolved with defaults, if needed.
             */
            const expectedResolvedMockParams = {
                ...unresolvedMockUserParams,
                multiroundProfile: defaultMultiroundProfile,
                systemPrompt: MockLLMService.systemPromptToOverrideWith,
                workerId: 0,
                resolvedWithMockLLMService: true,
            } as MockLLMModelParams;

            const actualResolvedMockParams = mockService.resolveParameters(
                unresolvedMockUserParams
            );
            expect(actualResolvedMockParams).toEqual(
                expectedResolvedMockParams
            );
        } finally {
            mockService.dispose();
        }
    });
});
