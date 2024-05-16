import { expect } from "earl";

import { ConfigurationError } from "../../../llm/llmServiceErrors";
import { ErrorsHandlingMode } from "../../../llm/llmServices/llmService";
import { PredefinedProofsModelParams } from "../../../llm/llmServices/modelParams";
import { PredefinedProofsService } from "../../../llm/llmServices/predefinedProofs/predefinedProofsService";
import { timeZero } from "../../../llm/llmServices/utils/time";
import { ProofGenerationContext } from "../../../llm/proofGenerationContext";
import { PredefinedProofsUserModelParams } from "../../../llm/userModelParams";

import { EventLogger } from "../../../logging/eventLogger";
import { delay } from "../../commonTestFunctions/delay";
import { resolveParametersOrThrow } from "../../commonTestFunctions/resolveOrThrow";
import { withLLMService } from "../../commonTestFunctions/withLLMService";
import { testModelId } from "../llmSpecificTestUtils/constants";
import {
    EventsTracker,
    subscribeToTrackEvents,
} from "../llmSpecificTestUtils/eventsTracker";
import { expectLogs } from "../llmSpecificTestUtils/expectLogs";
import { testLLMServiceCompletesAdmitFromFile } from "../llmSpecificTestUtils/testAdmitCompletion";
import { testResolveParametersFailsWithSingleCause } from "../llmSpecificTestUtils/testResolveParameters";

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
        block: (
            predefinedProofsService: PredefinedProofsService,
            testEventLogger: EventLogger
        ) => Promise<void>
    ) {
        const testEventLogger = new EventLogger();
        return withLLMService(
            new PredefinedProofsService(testEventLogger, true),
            async (predefinedProofsService) => {
                return block(predefinedProofsService, testEventLogger);
            }
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
        ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS,
        ErrorsHandlingMode.RETHROW_ERRORS,
    ].forEach((errorsHandlingMode) => {
        test(`Test generation logging: ${errorsHandlingMode}`, async () => {
            await withPredefinedProofsService(
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
                    try {
                        await predefinedProofsService.generateProof(
                            proofGenerationContext,
                            resolvedParams,
                            resolvedParams.tactics.length + 1,
                            errorsHandlingMode
                        );
                    } catch (e) {
                        expect(errorsHandlingMode).toEqual(
                            ErrorsHandlingMode.RETHROW_ERRORS
                        );
                        const error = e as ConfigurationError;
                        expect(error).toBeTruthy();
                    }

                    const expectedEvents: EventsTracker = {
                        successfulRequestEventsN: 0,
                        failedRequestEventsN:
                            errorsHandlingMode ===
                            ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS
                                ? 1
                                : 0,
                    };
                    expect(eventsTracker).toEqual(expectedEvents);

                    // ConfigurationError should not be logged!
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

    test("Test `resolveParameters` validates PredefinedProofs-extended params (`tactics`)", async () => {
        await withPredefinedProofsService(async (predefinedProofsService) => {
            testResolveParametersFailsWithSingleCause(
                predefinedProofsService,
                {
                    ...inputParams,
                    tactics: [],
                },
                "tactics"
            );
        });
    });

    test("Test `generateProof` throws on invalid `choices`", async () => {
        await withPredefinedProofsService(async (predefinedProofsService) => {
            const resolvedParams = resolveParametersOrThrow(
                predefinedProofsService,
                inputParams
            );

            // non-positive choices
            expect(async () => {
                await predefinedProofsService.generateProof(
                    proofGenerationContext,
                    resolvedParams,
                    -1,
                    ErrorsHandlingMode.RETHROW_ERRORS
                );
            }).toBeRejectedWith(ConfigurationError, "choices");

            // choices > tactics.length
            expect(async () => {
                await predefinedProofsService.generateProof(
                    proofGenerationContext,
                    resolvedParams,
                    resolvedParams.tactics.length + 1,
                    ErrorsHandlingMode.RETHROW_ERRORS
                );
            }).toBeRejectedWith(ConfigurationError, "choices");
        });
    });

    test("Test chat-related features throw", async () => {
        await withPredefinedProofsService(async (predefinedProofsService) => {
            const resolvedParams = resolveParametersOrThrow(
                predefinedProofsService,
                inputParams
            );
            expect(async () => {
                await predefinedProofsService.generateFromChat(
                    {
                        chat: [],
                        estimatedTokens: 0,
                    },
                    resolvedParams,
                    choices,
                    ErrorsHandlingMode.RETHROW_ERRORS
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
            expect(
                async () =>
                    await generatedProof.fixProof(
                        "pretend to be diagnostic",
                        3,
                        ErrorsHandlingMode.RETHROW_ERRORS
                    )
            ).toBeRejectedWith(ConfigurationError, "cannot be fixed");
        });
    });

    test("Test time to become available is zero", async () => {
        await withPredefinedProofsService(async (predefinedProofsService) => {
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
                cursedParams.tactics.length,
                ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS
            );
            await delay(4000);
            await predefinedProofsService.generateProof(
                proofGenerationContext,
                cursedParams,
                cursedParams.tactics.length,
                ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS
            );
            // despite 2 failures with >= 4 secs interval, should be available right now
            expect(
                predefinedProofsService.estimateTimeToBecomeAvailable()
            ).toEqual(timeZero);
        });
    }).timeout(6000);
});
