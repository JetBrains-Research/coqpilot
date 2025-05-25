import { expect } from "earl";

import { ErrorsHandlingMode } from "../../../proofProviders/impl/commonStructures/errorsHandlingMode";
import {
    ModelParams,
    MultiroundProfile,
    modelParamsSchema,
} from "../../../proofProviders/impl/modelParams";
import {
    BasicModelParamsResolver,
    defaultMaxContextTheoremsNumber,
    defaultMultiroundProfile,
    defaultSystemMessageContent,
} from "../../../proofProviders/impl/utils/paramsResolvers/kit/basicModelParamsResolvers";
import { UserModelParams } from "../../../proofProviders/userModelParams";

import { withProofProvider } from "../../commonTestFunctions/withProofProvider";
import { testModelId } from "../proofProvidersSpecificTestUtils/constants";
import {
    MockService,
    MockServiceModelParams,
    MockServiceUserModelParams,
} from "../proofProvidersSpecificTestUtils/mockService";

suite("[ProofProvider] Test model-params resolution", () => {
    function testBasicResolverSucceeded(
        testName: string,
        inputParamsAddOns: Partial<UserModelParams> = {},
        expectedResolvedParamsAddOns: Partial<ModelParams> = {}
    ) {
        test(testName, () => {
            const inputParams: UserModelParams = {
                modelId: testModelId,
                choices: 1,
                // `systemPrompt` will be resolved with default
                maxTokensToGenerate: 100,
                tokensLimit: 1000,
                // `maxContextTheoremsNumber` will be resolved with default
                multiroundProfile: {
                    proofFixChoices: 3,
                    // `maxRoundsNumber`, `proofFixPrompt` and `maxPreviousProofVersionsNumber` will be resolved with defaults
                },
                ...inputParamsAddOns,
            };
            const modelParamsResolver = new BasicModelParamsResolver(
                modelParamsSchema,
                "ModelParams"
            );
            const resolutionResult = modelParamsResolver.resolve(inputParams);

            const expectedResolvedParams: ModelParams = {
                modelId: testModelId,
                systemPrompt: defaultSystemMessageContent,
                maxTokensToGenerate: 100,
                tokensLimit: 1000,
                maxContextTheoremsNumber: defaultMaxContextTheoremsNumber,
                multiroundProfile: {
                    maxRoundsNumber: defaultMultiroundProfile.maxRoundsNumber,
                    defaultProofFixChoices: 3,
                    proofFixPrompt: defaultMultiroundProfile.proofFixPrompt,
                    maxPreviousProofVersionsNumber:
                        defaultMultiroundProfile.maxPreviousProofVersionsNumber,
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
        const modelParamsResolver = new BasicModelParamsResolver(
            modelParamsSchema,
            "ModelParams"
        );
        const resolutionResult = modelParamsResolver.resolve(inputParams);

        expect(resolutionResult.resolved).toBeNullish();
        const expectedNumberOfFailedParams = 5;
        expect(
            resolutionResult.resolutionLogs.filter(
                (paramLog) => paramLog.isInvalidCause !== undefined
            )
        ).toHaveLength(expectedNumberOfFailedParams);
    });

    test("Test resolution by ProofProvider", async () => {
        await withProofProvider(
            new MockService(undefined, ErrorsHandlingMode.RETHROW_ERRORS),
            async (mockService) => {
                const unresolvedMockUserParams: MockServiceUserModelParams = {
                    modelId: testModelId,
                    systemPrompt:
                        "This system prompt will be overriden by the proofProvider",
                    maxTokensToGenerate: 100,
                    tokensLimit: 1000,
                    proofsToGenerate: ["auto.", "avto."],
                };

                /*
                 * `MockService` parameters resolution does 4 changes to `inputParams`:
                 * - resolves undefined `workerId` to 0;
                 * - adds extra `resolvedWithMockService: true` property;
                 * - overrides original `systemPrompt` with `this.systemPromptToOverrideWith`.
                 * - overrides original `choices` to `defaultChoices` with `proofsToGenerate.length`.
                 * Everything else should be resolved with defaults, if needed.
                 */
                const expectedResolvedMockParams = {
                    ...unresolvedMockUserParams,
                    maxContextTheoremsNumber: defaultMaxContextTheoremsNumber,
                    multiroundProfile: defaultMultiroundProfile,
                    systemPrompt: MockService.systemPromptToOverrideWith,
                    workerId: 0,
                    resolvedWithMockService: true,
                    defaultChoices: 2,
                } as MockServiceModelParams;

                const actualResolvedMockParams = mockService.resolveParameters(
                    unresolvedMockUserParams
                ).resolved;

                expect(actualResolvedMockParams).toEqual(
                    expectedResolvedMockParams
                );
            }
        );
    });
});
