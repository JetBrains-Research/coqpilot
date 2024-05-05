import { expect } from "earl";

import {
    ConfigurationError,
    GenerationFailedError,
    LLMServiceError,
} from "../../../llm/llmServiceErrors";
import { AnalyzedChatHistory } from "../../../llm/llmServices/chat";
import { ErrorsHandlingMode } from "../../../llm/llmServices/llmService";

import { subscribeToTrackMockEvents } from "./eventsTracker";
import { ExpectedRecord, expectLogs } from "./expectLogs";
import { MockLLMModelParams, MockLLMService } from "./mockLLMService";
import { withMockLLMService } from "./withMockLLMService";

export function testFailedGenerationCompletely<T>(
    generate: (
        mockService: MockLLMService,
        mockParams: MockLLMModelParams,
        errorsHandlingMode: ErrorsHandlingMode,
        preparedData?: T
    ) => Promise<string[]>,
    additionalTestParams: any = {},
    prepareDataBeforeTest?: (
        mockService: MockLLMService,
        basicMockParams: MockLLMModelParams
    ) => Promise<T>
) {
    buildErrorsWithExpectedHandling().forEach(
        ({ error, expectedThrownError, expectedLogs }) => {
            const commonTestParams = {
                failureName: error.constructor.name,
                expectedGenerationLogs: expectedLogs,

                errorToThrow: error,
                expectedErrorOfFailedEvent: expectedThrownError,

                shouldFailBeforeGenerationIsStarted: false,

                ...additionalTestParams,
            };
            testFailedGeneration(
                {
                    ...commonTestParams,
                    errorsHandlingMode:
                        ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS,
                    expectedFailedGenerationEventsN: 1,
                },
                generate,
                prepareDataBeforeTest
            );

            testFailedGeneration(
                {
                    ...commonTestParams,
                    errorsHandlingMode: ErrorsHandlingMode.RETHROW_ERRORS,
                    // `ErrorsHandlingMode.RETHROW_ERRORS` doesn't use failed-generation events
                    expectedFailedGenerationEventsN: 0,

                    expectedThrownError: expectedThrownError,
                },
                generate,
                prepareDataBeforeTest
            );
        }
    );
}

export interface ErrorWithExpectedHandling {
    error: Error;
    expectedThrownError: LLMServiceError;
    expectedLogs: ExpectedRecord[];
}

export function buildErrorsWithExpectedHandling(): ErrorWithExpectedHandling[] {
    const internalError = Error("internal generation error");
    const configurationError = new ConfigurationError(
        "something is wrong with params"
    );
    const generationFailedError = new GenerationFailedError(
        Error("implementation decided to throw wrapped error by itself")
    );

    return [
        {
            error: internalError,
            expectedThrownError: new GenerationFailedError(internalError),
            expectedLogs: [{ status: "FAILURE", error: internalError }],
        },
        {
            error: configurationError,
            expectedThrownError: configurationError,
            expectedLogs: [],
        },
        {
            error: generationFailedError,
            expectedThrownError: generationFailedError,
            expectedLogs: [
                { status: "FAILURE", error: generationFailedError.cause },
            ],
        },
    ];
}

export function testFailureAtChatBuilding<T>(
    generate: (
        mockService: MockLLMService,
        mockParams: MockLLMModelParams,
        errorsHandlingMode: ErrorsHandlingMode,
        preparedData?: T
    ) => Promise<string[]>,
    additionalTestParams: any = {},
    prepareDataBeforeTest?: (
        mockService: MockLLMService,
        basicMockParams: MockLLMModelParams
    ) => Promise<T>
) {
    testFailedGeneration(
        {
            errorsHandlingMode:
                ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS,
            failureName: "failure at chat building",
            expectedGenerationLogs: [],
            expectedFailedGenerationEventsN: 1,
            buildErroneousMockParams: (basicMockParams: MockLLMModelParams) => {
                return {
                    ...basicMockParams,
                    maxTokensToGenerate: 100,
                    tokensLimit: 10,
                };
            },
            shouldFailBeforeGenerationIsStarted: true,
            ...additionalTestParams,
        },
        generate,
        prepareDataBeforeTest
    );
}

export interface FailedGenerationTestParams {
    errorsHandlingMode: ErrorsHandlingMode;
    failureName: string;
    expectedGenerationLogs: ExpectedRecord[];
    expectedFailedGenerationEventsN: number;

    errorToThrow?: Error;
    expectedErrorOfFailedEvent?: LLMServiceError;
    expectedThrownError?: LLMServiceError;

    expectedChatOfMockEvent?: AnalyzedChatHistory;

    buildErroneousMockParams?: (
        basicMockParams: MockLLMModelParams
    ) => MockLLMModelParams;
    shouldFailBeforeGenerationIsStarted: boolean;

    proofsToGenerate?: string[];

    testTargetName?: string;
}

export function testFailedGeneration<T>(
    testParams: FailedGenerationTestParams,
    generate: (
        mockService: MockLLMService,
        mockParams: MockLLMModelParams,
        errorsHandlingMode: ErrorsHandlingMode,
        preparedData?: T
    ) => Promise<string[]>,
    prepareDataBeforeTest?: (
        mockService: MockLLMService,
        basicMockParams: MockLLMModelParams
    ) => Promise<T>
) {
    const testNamePrefix =
        testParams.testTargetName ?? "Test failed generation";
    test(`${testNamePrefix}: ${testParams.failureName}, ${testParams.errorsHandlingMode}`, async () => {
        await withMockLLMService(
            async (mockService, basicMockParams, testEventLogger) => {
                const preparedData =
                    prepareDataBeforeTest !== undefined
                        ? await prepareDataBeforeTest(
                              mockService,
                              basicMockParams
                          )
                        : undefined;

                const eventsTracker = subscribeToTrackMockEvents(
                    testEventLogger,
                    mockService,
                    testParams.expectedChatOfMockEvent,
                    testParams.expectedErrorOfFailedEvent
                );

                if (testParams.errorToThrow !== undefined) {
                    mockService.throwErrorOnNextGeneration(
                        testParams.errorToThrow
                    );
                }
                const maybeErroneousMockParams =
                    testParams.buildErroneousMockParams !== undefined
                        ? testParams.buildErroneousMockParams(basicMockParams)
                        : basicMockParams;

                try {
                    const noGeneratedProofs = await generate(
                        mockService,
                        maybeErroneousMockParams,
                        testParams.errorsHandlingMode,
                        preparedData
                    );
                    expect(testParams.errorsHandlingMode).toEqual(
                        ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS
                    );
                    expect(noGeneratedProofs).toHaveLength(0);
                } catch (e) {
                    expect(testParams.errorsHandlingMode).toEqual(
                        ErrorsHandlingMode.RETHROW_ERRORS
                    );
                    expect(e as LLMServiceError).toBeTruthy();
                    if (testParams.expectedThrownError !== undefined) {
                        expect(e).toEqual(testParams.expectedThrownError);
                    }
                }

                const expectedMockEventsN =
                    testParams.shouldFailBeforeGenerationIsStarted ? 0 : 1;
                expect(eventsTracker).toEqual({
                    mockGenerationEventsN: expectedMockEventsN,
                    successfulGenerationEventsN: 0,
                    failedGenerationEventsN:
                        testParams.expectedFailedGenerationEventsN,
                });
                expectLogs(testParams.expectedGenerationLogs, mockService);

                // check if service stays available after an error occurred
                const generatedProofs = await generate(
                    mockService,
                    basicMockParams,
                    testParams.errorsHandlingMode,
                    preparedData
                );
                if (testParams.proofsToGenerate !== undefined) {
                    expect(generatedProofs).toEqual(
                        testParams.proofsToGenerate
                    );
                }

                expect(eventsTracker).toEqual({
                    mockGenerationEventsN: expectedMockEventsN + 1,
                    successfulGenerationEventsN: 1,
                    failedGenerationEventsN:
                        testParams.expectedFailedGenerationEventsN,
                });
                // `mockLLM` was created with `debugLogs = true`, so logs are not cleaned on success
                expectLogs(
                    [
                        ...testParams.expectedGenerationLogs,
                        { status: "SUCCESS" },
                    ],
                    mockService
                );
            }
        );
    });
}
