import { expect } from "earl";

import {
    ModelParams,
    MultiroundProfile,
} from "../../../../llm/llmServices/modelParams";
import {
    BasicModelParamsResolver,
    defaultMultiroundProfile,
    defaultSystemMessageContent,
} from "../../../../llm/llmServices/modelParamsResolvers";
import { UserModelParams } from "../../../../llm/userModelParams";

import { withLLMService } from "../../../commonTestFunctions/withLLMService";
import { testModelId } from "../../llmSpecificTestUtils/constants";
import {
    MockLLMModelParams,
    MockLLMService,
    MockLLMUserModelParams,
} from "../../llmSpecificTestUtils/mockLLMService";
import {
    ModelParamsAddOns,
    UserModelParamsAddOns,
} from "../../llmSpecificTestUtils/transformParams";

suite("[LLMService] Test model-params resolution", () => {
    function testBasicResolverSucceeded(
        testName: string,
        inputParamsAddOns: UserModelParamsAddOns = {},
        expectedResolvedParamsAddOns: ModelParamsAddOns = {}
    ) {
        test(testName, () => {
            const inputParams: UserModelParams = {
                modelId: testModelId,
                choices: 1,
                // `systemPrompt` will be resolved with default
                maxTokensToGenerate: 100,
                tokensLimit: 1000,
                multiroundProfile: {
                    proofFixChoices: 3,
                    // `maxRoundsNumber` and `proofFixPrompt` will be resolved with defaults
                },
                ...inputParamsAddOns,
            };
            const modelParamsResolver = new BasicModelParamsResolver();
            const resolutionResult = modelParamsResolver.resolve(inputParams);

            const expectedResolvedParams: ModelParams = {
                modelId: testModelId,
                systemPrompt: defaultSystemMessageContent,
                maxTokensToGenerate: 100,
                tokensLimit: 1000,
                multiroundProfile: {
                    maxRoundsNumber: defaultMultiroundProfile.maxRoundsNumber,
                    defaultProofFixChoices: 3,
                    proofFixPrompt: defaultMultiroundProfile.proofFixPrompt,
                } as MultiroundProfile,
                defaultChoices: 1,
                ...expectedResolvedParamsAddOns,
            } as ModelParams;
            expect(resolutionResult.resolved).toEqual(expectedResolvedParams);
        });
    }

    testBasicResolverSucceeded(
        "Test basic resolver: successfully resolves with defaults"
    );

    testBasicResolverSucceeded(
        "Test basic resolver: resolves undefined `multiroundProfile`",
        {
            multiroundProfile: undefined,
        },
        {
            multiroundProfile: defaultMultiroundProfile,
        }
    );

    test("Test basic resolver: reports failed parameters", () => {
        const inputParams: UserModelParams = {
            modelId: testModelId,
            choices: undefined, // fail
            systemPrompt: "Generate proof!",
            maxTokensToGenerate: -1, // fail
            tokensLimit: -1, // fail
            multiroundProfile: {
                maxRoundsNumber: -1, // fail
                proofFixChoices: -1, // fail
                proofFixPrompt: "Fix proof!",
            },
        };
        const modelParamsResolver = new BasicModelParamsResolver();
        const resolutionResult = modelParamsResolver.resolve(inputParams);

        expect(resolutionResult.resolved).toBeNullish();
        const expectedNumberOfFailedParams = 5;
        expect(
            resolutionResult.resolutionLogs.filter(
                (paramLog) => paramLog.isInvalidCause !== undefined
            )
        ).toHaveLength(expectedNumberOfFailedParams);
    });

    test("Test resolution by LLMService", async () => {
        await withLLMService(new MockLLMService(), async (mockService) => {
            const unresolvedMockUserParams: MockLLMUserModelParams = {
                modelId: testModelId,
                systemPrompt: "This system prompt will be overriden by service",
                maxTokensToGenerate: 100,
                tokensLimit: 1000,
                proofsToGenerate: ["auto.", "avto."],
            };

            /*
             * `MockLLMService` parameters resolution does 4 changes to `inputParams`:
             * - resolves undefined `workerId` to 0;
             * - adds extra `resolvedWithMockLLMService: true` property;
             * - overrides original `systemPrompt` with `this.systemPromptToOverrideWith`.
             * - overrides original `choices` to `defaultChoices` with `proofsToGenerate.length`.
             * Everything else should be resolved with defaults, if needed.
             */
            const expectedResolvedMockParams = {
                ...unresolvedMockUserParams,
                multiroundProfile: defaultMultiroundProfile,
                systemPrompt: MockLLMService.systemPromptToOverrideWith,
                workerId: 0,
                resolvedWithMockLLMService: true,
                defaultChoices: 2,
            } as MockLLMModelParams;

            const actualResolvedMockParams = mockService.resolveParameters(
                unresolvedMockUserParams
            ).resolved;

            expect(actualResolvedMockParams).toEqual(
                expectedResolvedMockParams
            );
        });
    });
});
