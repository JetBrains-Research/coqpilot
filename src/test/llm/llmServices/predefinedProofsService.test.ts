import { expect } from "earl";

import { InvalidRequestError } from "../../../llm/llmServiceErrors";
import { ErrorsHandlingMode } from "../../../llm/llmServices/llmService";
import { PredefinedProofsModelParams } from "../../../llm/llmServices/modelParams";
import { PredefinedProofsService } from "../../../llm/llmServices/predefinedProofs/predefinedProofsService";
import { timeZero } from "../../../llm/llmServices/utils/time";
import { ProofGenerationContext } from "../../../llm/proofGenerationContext";
import { PredefinedProofsUserModelParams } from "../../../llm/userModelParams";

import { EventLogger } from "../../../logging/eventLogger";
import { delay } from "../../commonTestFunctions/delay";
import {
    EventsTracker,
    subscribeToTrackEvents,
} from "../llmSpecificTestUtils/eventsTracker";
import { expectLogs } from "../llmSpecificTestUtils/expectLogs";
import { testLLMServiceCompletesAdmitFromFile } from "../llmSpecificTestUtils/testAdmitCompletion";

suite("[LLMService] Test `PredefinedProofsService`", function () {
    const simpleTactics = ["auto.", "intros.", "reflexivity."];
    const userParams: PredefinedProofsUserModelParams = {
        modelName: "predefine proofs",
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
        const predefinedProofsService = new PredefinedProofsService(
            testEventLogger,
            true
        );
        try {
            await block(predefinedProofsService, testEventLogger);
        } finally {
            predefinedProofsService.dispose();
        }
    }

    const choices = simpleTactics.length;
    const inputFile = ["small_document.v"];

    test("Simple generation: prove with `auto.`", async () => {
        const predefinedProofsService = new PredefinedProofsService();
        await testLLMServiceCompletesAdmitFromFile(
            predefinedProofsService,
            userParams,
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
                        predefinedProofsService
                    );
                    const resolvedParams =
                        predefinedProofsService.resolveParameters(
                            userParams
                        ) as PredefinedProofsModelParams;

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
                        const error = e as InvalidRequestError;
                        expect(error).toBeTruthy();
                    }

                    const expectedEvents: EventsTracker = {
                        successfulGenerationEventsN: 0,
                        failedGenerationEventsN:
                            errorsHandlingMode ===
                            ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS
                                ? 1
                                : 0,
                    };
                    expect(eventsTracker).toEqual(expectedEvents);
                    expectLogs([{ status: "FAILED" }], predefinedProofsService);

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

                    expectedEvents.successfulGenerationEventsN += 1;
                    expect(eventsTracker).toEqual(expectedEvents);
                    expectLogs(
                        [{ status: "FAILED" }, { status: "SUCCESS" }],
                        predefinedProofsService
                    );
                }
            );
        });
    });

    test("Test chat-related features throw", async () => {
        await withPredefinedProofsService(
            async (predefinedProofsService, _testEventLogger) => {
                const resolvedParams =
                    predefinedProofsService.resolveParameters(userParams);
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
                }).toBeRejected();

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
                ).toBeRejected();
            }
        );
    });

    test("Test time to become available is zero", async () => {
        await withPredefinedProofsService(
            async (predefinedProofsService, _testEventLogger) => {
                const resolvedParams =
                    predefinedProofsService.resolveParameters(
                        userParams
                    ) as PredefinedProofsModelParams;
                await predefinedProofsService.generateProof(
                    proofGenerationContext,
                    resolvedParams,
                    resolvedParams.tactics.length + 1,
                    ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS
                );
                await delay(4000);
                await predefinedProofsService.generateProof(
                    proofGenerationContext,
                    resolvedParams,
                    resolvedParams.tactics.length + 1,
                    ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS
                );
                // despite 2 failures with >= 4 secs interval, should be available right now
                expect(
                    predefinedProofsService.estimateTimeToBecomeAvailable()
                ).toEqual(timeZero);
            }
        );
    }).timeout(6000);
});