import { expect } from "earl";

import { ConfigurationError } from "../../../llm/llmServiceErrors";
import { ErrorsHandlingMode } from "../../../llm/llmServices/commonStructures/errorsHandlingMode";
import { ProofGenerationMetadataHolder } from "../../../llm/llmServices/commonStructures/proofGenerationMetadata";
import { PredefinedProofsModelParams } from "../../../llm/llmServices/modelParams";
import { PredefinedProofsService } from "../../../llm/llmServices/predefinedProofs/predefinedProofsService";
import { resolveParametersOrThrow } from "../../../llm/llmServices/utils/resolveOrThrow";
import { ProofGenerationContext } from "../../../llm/proofGenerationContext";
import { PredefinedProofsUserModelParams } from "../../../llm/userModelParams";

import { EventLogger } from "../../../logging/eventLogger";
import { delay } from "../../../utils/delay";
import { timeZero } from "../../../utils/time";
import { withLLMService } from "../../commonTestFunctions/withLLMService";
import { testModelId } from "../llmSpecificTestUtils/constants";
import {
    EventsTracker,
    subscribeToTrackEvents,
} from "../llmSpecificTestUtils/eventsTracker";
import { expectLogs } from "../llmSpecificTestUtils/expectLogs";
import { testLLMServiceCompletesAdmitFromFile } from "../llmSpecificTestUtils/testAdmitCompletion";
import {
    testResolveParametersFailsWithSingleCause,
    testResolveValidCompleteParameters,
} from "../llmSpecificTestUtils/testResolveParameters";

suite("[LLMService] Test `PredefinedProofsService`", function () {
    const simpleTactics = ["auto.", "intros.", "reflexivity."];
    const inputParams: PredefinedProofsUserModelParams = {
        modelId: testModelId,
        tactics: simpleTactics,
    };
    const proofGenerationContext: ProofGenerationContext = {
        completionTarget: "could be anything",
        contextTheorems: [],
    };

    async function withPredefinedProofsService(
        errorsHandlingMode: ErrorsHandlingMode,
        block: (
            predefinedProofsService: PredefinedProofsService,
            testEventLogger: EventLogger
        ) => Promise<void>
    ) {
        const testEventLogger = new EventLogger();
        return withLLMService(
            new PredefinedProofsService(
                testEventLogger,
                errorsHandlingMode,
                undefined,
                true
            ),
            async (predefinedProofsService) => {
                return block(predefinedProofsService, testEventLogger);
            }
        );
    }

    async function withDefaultPredefinedProofsService(
        block: (
            predefinedProofsService: PredefinedProofsService,
            testEventLogger: EventLogger
        ) => Promise<void>
    ) {
        return withPredefinedProofsService(
            ErrorsHandlingMode.RETHROW_ERRORS,
            block
        );
    }

    const choices = simpleTactics.length;
    const inputFile = ["small_document.v"];

    test("Simple generation: prove with `auto.`", async () => {
        const predefinedProofsService = new PredefinedProofsService();
        await testLLMServiceCompletesAdmitFromFile(
            predefinedProofsService,
            inputParams,
            inputFile,
            choices
        );
    });

    [
        ErrorsHandlingMode.SWALLOW_ERRORS,
        ErrorsHandlingMode.RETHROW_ERRORS,
    ].forEach((errorsHandlingMode) => {
        test(`Test generation logging: ${errorsHandlingMode}`, async () => {
            await withPredefinedProofsService(
                errorsHandlingMode,
                async (predefinedProofsService, testEventLogger) => {
                    const eventsTracker = subscribeToTrackEvents(
                        testEventLogger,
                        predefinedProofsService,
                        inputParams.modelId
                    );
                    const resolvedParams = resolveParametersOrThrow(
                        predefinedProofsService,
                        inputParams
                    );

                    // failed generation
                    const failedMetadataHolder =
                        new ProofGenerationMetadataHolder();
                    try {
                        await predefinedProofsService.generateProof(
                            proofGenerationContext,
                            resolvedParams,
                            resolvedParams.tactics.length + 1,
                            failedMetadataHolder
                        );
                        expect(errorsHandlingMode).toEqual(
                            ErrorsHandlingMode.SWALLOW_ERRORS
                        );
                    } catch (e) {
                        expect(errorsHandlingMode).toEqual(
                            ErrorsHandlingMode.RETHROW_ERRORS
                        );
                        expect(e instanceof ConfigurationError).toBeTruthy();
                    }
                    const failedMetadata =
                        failedMetadataHolder.getFailedProofGenerationMetadata();
                    expect(failedMetadata.analyzedChat).toBeNullish();
                    expect(
                        failedMetadata.llmServiceError instanceof
                            ConfigurationError
                    ).toBeTruthy();

                    const expectedEvents: EventsTracker = {
                        successfulRequestEventsN: 0,
                        failedRequestEventsN: 1,
                    };
                    expect(eventsTracker).toEqual(expectedEvents);

                    // `ConfigurationError` should not be logged!
                    expectLogs([], predefinedProofsService);

                    // successful generation
                    const generatedProofs =
                        await predefinedProofsService.generateProof(
                            proofGenerationContext,
                            resolvedParams,
                            resolvedParams.tactics.length
                        );
                    expect(generatedProofs).toHaveLength(
                        resolvedParams.tactics.length
                    );

                    expectedEvents.successfulRequestEventsN += 1;
                    expect(eventsTracker).toEqual(expectedEvents);
                    expectLogs(
                        [{ status: "SUCCESS" }],
                        predefinedProofsService
                    );
                }
            );
        });
    });

    test("Test `resolveParameters` reads & accepts valid params", async () => {
        await withDefaultPredefinedProofsService(
            async (predefinedProofsService) => {
                testResolveValidCompleteParameters(
                    predefinedProofsService,
                    inputParams
                );
            }
        );
    });

    test("Test `resolveParameters` validates PredefinedProofs-extended params (`tactics`)", async () => {
        await withDefaultPredefinedProofsService(
            async (predefinedProofsService) => {
                testResolveParametersFailsWithSingleCause(
                    predefinedProofsService,
                    {
                        ...inputParams,
                        tactics: [],
                    },
                    "tactics"
                );
            }
        );
    });

    test("Test `resolveParameters` overrides params correctly", async () => {
        await withDefaultPredefinedProofsService(
            async (predefinedProofsService) => {
                const resolutionResult =
                    predefinedProofsService.resolveParameters({
                        ...inputParams,
                        choices: 1,
                        systemPrompt: "asking for something",
                        maxTokensToGenerate: 2000,
                        tokensLimit: 4000,
                        maxContextTheoremsNumber: 20,
                        multiroundProfile: {
                            maxRoundsNumber: 10,
                            proofFixChoices: 5,
                            proofFixPrompt: "asking for more of something",
                            maxPreviousProofVersionsNumber: 2,
                        },
                    });

                // first, verify all params were read correctly
                for (const paramLog of resolutionResult.resolutionLogs) {
                    expect(paramLog.isInvalidCause).toBeNullish();
                    expect(
                        paramLog.inputReadCorrectly.wasPerformed
                    ).toBeTruthy();
                    // expect(paramLog.overriden).toBeTruthy(); // is not true for mock overrides
                    expect(
                        paramLog.resolvedWithDefault.wasPerformed
                    ).toBeFalsy();
                }

                expect(resolutionResult.resolved).toEqual({
                    modelId: testModelId,
                    tactics: simpleTactics,
                    systemPrompt: "",
                    maxTokensToGenerate: Math.max(
                        0,
                        ...simpleTactics.map((tactic) => tactic.length)
                    ),
                    tokensLimit: Number.MAX_SAFE_INTEGER,
                    maxContextTheoremsNumber: Number.MAX_SAFE_INTEGER,
                    multiroundProfile: {
                        maxRoundsNumber: 1,
                        defaultProofFixChoices: 0,
                        proofFixPrompt: "",
                        maxPreviousProofVersionsNumber: 0,
                    },
                    defaultChoices: simpleTactics.length,
                });
            }
        );
    });

    test("Test `generateProof` throws on invalid `choices`", async () => {
        await withPredefinedProofsService(
            ErrorsHandlingMode.RETHROW_ERRORS,
            async (predefinedProofsService) => {
                const resolvedParams = resolveParametersOrThrow(
                    predefinedProofsService,
                    inputParams
                );

                // non-positive choices
                await expect(async () => {
                    await predefinedProofsService.generateProof(
                        proofGenerationContext,
                        resolvedParams,
                        -1
                    );
                }).toBeRejectedWith(ConfigurationError, "choices");

                // choices > tactics.length
                await expect(async () => {
                    await predefinedProofsService.generateProof(
                        proofGenerationContext,
                        resolvedParams,
                        resolvedParams.tactics.length + 1
                    );
                }).toBeRejectedWith(ConfigurationError, "choices");
            }
        );
    });

    test("Test chat-related features throw", async () => {
        await withPredefinedProofsService(
            ErrorsHandlingMode.RETHROW_ERRORS,
            async (predefinedProofsService) => {
                const resolvedParams = resolveParametersOrThrow(
                    predefinedProofsService,
                    inputParams
                );
                await expect(async () => {
                    await predefinedProofsService.generateFromChat(
                        {
                            chat: [],
                            contextTheorems: [],
                            estimatedTokens: {
                                messagesTokens: 0,
                                maxTokensToGenerate: 0,
                                maxTokensInTotal: 0,
                            },
                        },
                        resolvedParams,
                        choices
                    );
                }).toBeRejectedWith(
                    ConfigurationError,
                    "does not support generation from chat"
                );

                const [generatedProof] =
                    await predefinedProofsService.generateProof(
                        proofGenerationContext,
                        resolvedParams,
                        1
                    );
                expect(generatedProof.canBeFixed()).toBeFalsy();
                await expect(
                    async () =>
                        await generatedProof.fixProof(
                            "pretend to be diagnostic",
                            3
                        )
                ).toBeRejectedWith(ConfigurationError, "cannot be fixed");
            }
        );
    });

    test("Test time to become available is zero", async () => {
        await withPredefinedProofsService(
            ErrorsHandlingMode.SWALLOW_ERRORS,
            async (predefinedProofsService) => {
                const resolvedParams = resolveParametersOrThrow(
                    predefinedProofsService,
                    inputParams
                );
                const cursedParams: PredefinedProofsModelParams = {
                    ...resolvedParams,
                    tactics: [
                        "auto.",
                        () => {
                            throw Error("a curse");
                        },
                    ] as any[],
                };
                await predefinedProofsService.generateProof(
                    proofGenerationContext,
                    cursedParams,
                    cursedParams.tactics.length
                );
                await delay(4000);
                await predefinedProofsService.generateProof(
                    proofGenerationContext,
                    cursedParams,
                    cursedParams.tactics.length
                );
                // despite 2 failures with >= 4 secs interval, should be available right now
                expect(
                    predefinedProofsService.estimateTimeToBecomeAvailable()
                ).toEqual(timeZero);
            }
        );
    }).timeout(6000);
});
