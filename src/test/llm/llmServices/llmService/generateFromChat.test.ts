import { expect } from "earl";

import { GenerationFromChatFailedError } from "../../../../llm/llmServiceErrors";
import { ErrorsHandlingMode } from "../../../../llm/llmServices/llmService";

import {
    MockLLMModelParams,
    MockLLMService,
} from "../../testUtils/mockLLMService";
import {
    ExpectedRecord,
    expectLogs,
    mockChat,
    proofsToGenerate,
    subscribeToTrackEvents,
    withMockLLMService,
} from "../../testUtils/testGenerateProofPipeline";

suite("[LLMService] Test `generateFromChat`", () => {
    [
        ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS,
        ErrorsHandlingMode.RETHROW_ERRORS,
    ].forEach((errorsHandlingMode) => {
        test(`Test successful generation, ${errorsHandlingMode}`, async () => {
            await withMockLLMService(
                async (mockService, basicMockParams, testEventLogger) => {
                    const eventsTracker = subscribeToTrackEvents(
                        testEventLogger,
                        mockService,
                        mockChat
                    );

                    const generatedProofs = await mockService.generateFromChat(
                        mockChat,
                        basicMockParams,
                        proofsToGenerate.length,
                        errorsHandlingMode
                    );
                    expect(generatedProofs).toEqual(proofsToGenerate);

                    expect(eventsTracker).toEqual({
                        mockGenerationEventsN: 1,
                        successfulGenerationEventsN: 1,
                        failedGenerationEventsN: 0,
                    });
                    expectLogs([{ status: "SUCCESS" }], mockService);
                }
            );
        });
    });

    function testFailedGeneration(
        errorsHandlingMode: ErrorsHandlingMode,
        expectedFailedGenerationEventsN: number,
        testGenerationBlock: (
            mockService: MockLLMService,
            erroneousMockParams: MockLLMModelParams,
            internalGenerationError: Error
        ) => Promise<void>
    ) {
        test(`Test failed generation, ${errorsHandlingMode}`, async () => {
            await withMockLLMService(
                async (mockService, basicMockParams, testEventLogger) => {
                    const eventsTracker = subscribeToTrackEvents(
                        testEventLogger,
                        mockService,
                        mockChat
                    );

                    const internalGenerationError = Error(
                        "tokens limit exceeded"
                    );
                    mockService.throwErrorOnNextGeneration(
                        internalGenerationError
                    );
                    await testGenerationBlock(
                        mockService,
                        basicMockParams,
                        internalGenerationError
                    );

                    expect(eventsTracker).toEqual({
                        mockGenerationEventsN: 1,
                        successfulGenerationEventsN: 0,
                        failedGenerationEventsN:
                            expectedFailedGenerationEventsN,
                    });

                    const failureRecord: ExpectedRecord = {
                        status: "FAILED",
                        error: internalGenerationError,
                    };
                    expectLogs([failureRecord], mockService);

                    // check if service stays available after an error thrown
                    const generatedProofs = await mockService.generateFromChat(
                        mockChat,
                        basicMockParams,
                        proofsToGenerate.length,
                        errorsHandlingMode
                    );
                    expect(generatedProofs).toEqual(proofsToGenerate);
                    expect(eventsTracker).toEqual({
                        mockGenerationEventsN: 2,
                        successfulGenerationEventsN: 1,
                        failedGenerationEventsN:
                            expectedFailedGenerationEventsN,
                    });
                    // `mockLLM` was created with `debug = true`, so logs are not cleaned on success
                    expectLogs(
                        [failureRecord, { status: "SUCCESS" }],
                        mockService
                    );
                }
            );
        });
    }

    testFailedGeneration(
        ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS,
        1,
        async (mockService, erroneousMockParams, _internalGenerationError) => {
            const noGeneratedProofs = await mockService.generateFromChat(
                mockChat,
                erroneousMockParams,
                proofsToGenerate.length,
                ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS
            );
            expect(noGeneratedProofs).toHaveLength(0);
        }
    );

    testFailedGeneration(
        ErrorsHandlingMode.RETHROW_ERRORS,
        0, // `ErrorsHandlingMode.RETHROW_ERRORS` doesn't use failed-generation events
        async (mockService, erroneousMockParams, internalGenerationError) => {
            try {
                await mockService.generateFromChat(
                    mockChat,
                    erroneousMockParams,
                    proofsToGenerate.length,
                    ErrorsHandlingMode.RETHROW_ERRORS
                );
            } catch (e) {
                const wrappedError = e as GenerationFromChatFailedError;
                expect(wrappedError).toBeTruthy();
                expect(wrappedError.cause).toEqual(internalGenerationError);
            }
        }
    );
});
