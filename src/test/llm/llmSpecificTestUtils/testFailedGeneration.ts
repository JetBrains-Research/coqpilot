import { expect } from "earl";

import {
    ConfigurationError,
    GenerationFailedError,
    LLMServiceError,
} from "../../../llm/llmServiceErrors";
import { AnalyzedChatHistory } from "../../../llm/llmServices/commonStructures/chat";
import { ErrorsHandlingMode } from "../../../llm/llmServices/commonStructures/errorsHandlingMode";
import { ProofGenerationMetadataHolder } from "../../../llm/llmServices/commonStructures/proofGenerationMetadata";

import { subscribeToTrackMockEvents } from "./eventsTracker";
import { ExpectedRecord, expectLogs } from "./expectLogs";
import { MockLLMModelParams, MockLLMService } from "./mockLLMService";
import { withMockLLMService } from "./withMockLLMService";

export function testFailedGenerationCompletely<T>(
    generate: (
        mockService: MockLLMService,
        mockParams: MockLLMModelParams,
        metadataHolder: ProofGenerationMetadataHolder,
        preparedData?: T
    ) => Promise<string[]>,
    additionalTestParams: Partial<FailedGenerationTestParams> = {},
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
                    errorsHandlingMode: ErrorsHandlingMode.SWALLOW_ERRORS,
                    expectedFailedRequestEventsN: 1,
                },
                generate,
                prepareDataBeforeTest
            );
            testFailedGeneration(
                {
                    ...commonTestParams,
                    errorsHandlingMode: ErrorsHandlingMode.RETHROW_ERRORS,
                    expectedFailedRequestEventsN: 1,
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
        metadataHolder: ProofGenerationMetadataHolder,
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
            errorsHandlingMode: ErrorsHandlingMode.SWALLOW_ERRORS,
            failureName: "failure at chat building",
            expectedGenerationLogs: [],
            expectedFailedRequestEventsN: 1,
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
    expectedFailedRequestEventsN: number;

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
        metadataHolder: ProofGenerationMetadataHolder,
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
            testParams.errorsHandlingMode,
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
                    basicMockParams.modelId,
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

                const failureGenerationMetadataHolder =
                    new ProofGenerationMetadataHolder();
                try {
                    const noGeneratedProofs = await generate(
                        mockService,
                        maybeErroneousMockParams,
                        failureGenerationMetadataHolder,
                        preparedData
                    );
                    expect(testParams.errorsHandlingMode).toEqual(
                        ErrorsHandlingMode.SWALLOW_ERRORS
                    );
                    expect(noGeneratedProofs).toHaveLength(0);
                } catch (e) {
                    expect(testParams.errorsHandlingMode).toEqual(
                        ErrorsHandlingMode.RETHROW_ERRORS
                    );
                    expect(e instanceof LLMServiceError).toBeTruthy();
                    if (testParams.expectedThrownError !== undefined) {
                        expect(e).toEqual(testParams.expectedThrownError);
                    }
                }
                const failureMetadata =
                    failureGenerationMetadataHolder.getFailedProofGenerationMetadata();
                if (testParams.expectedThrownError !== undefined) {
                    expect(failureMetadata.llmServiceError).toEqual(
                        testParams.expectedThrownError
                    );
                }

                const expectedMockEventsN =
                    testParams.shouldFailBeforeGenerationIsStarted ? 0 : 1;
                expect(eventsTracker).toEqual({
                    mockEventsN: expectedMockEventsN,
                    successfulRequestEventsN: 0,
                    failedRequestEventsN:
                        testParams.expectedFailedRequestEventsN,
                });
                expectLogs(testParams.expectedGenerationLogs, mockService);

                // check if service stays available after an error occurred
                const successfulGenerationMetadataHolder =
                    new ProofGenerationMetadataHolder();
                const generatedProofs = await generate(
                    mockService,
                    basicMockParams,
                    successfulGenerationMetadataHolder,
                    preparedData
                );
                if (testParams.proofsToGenerate !== undefined) {
                    expect(generatedProofs).toEqual(
                        testParams.proofsToGenerate
                    );
                    expect(
                        successfulGenerationMetadataHolder
                            .getSuccessfulProofGenerationMetadata()
                            .generatedRawProofs.map(
                                (rawProof) => rawProof.content
                            )
                    ).toEqual(testParams.proofsToGenerate);
                }

                expect(eventsTracker).toEqual({
                    mockEventsN: expectedMockEventsN + 1,
                    successfulRequestEventsN: 1,
                    failedRequestEventsN:
                        testParams.expectedFailedRequestEventsN,
                });
                // `mockLLM` was created with `debugLogs = true`, so logs are not cleaned on success
                // TODO (test): should it be always created with `debugLogs` enabled?
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
