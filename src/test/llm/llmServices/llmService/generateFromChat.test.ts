import { expect } from "earl";

import { ErrorsHandlingMode } from "../../../../llm/llmServices/llmService";

import {
    mockChat,
    proofsToGenerate,
} from "../../llmSpecificTestUtils/constants";
import { subscribeToTrackMockEvents } from "../../llmSpecificTestUtils/eventsTracker";
import { expectLogs } from "../../llmSpecificTestUtils/expectLogs";
import {
    MockLLMModelParams,
    MockLLMService,
} from "../../llmSpecificTestUtils/mockLLMService";
import { testFailedGenerationCompletely } from "../../llmSpecificTestUtils/testFailedGeneration";
import { withMockLLMService } from "../../llmSpecificTestUtils/withMockLLMService";

suite("[LLMService] Test `generateFromChat`", () => {
    [
        ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS,
        ErrorsHandlingMode.RETHROW_ERRORS,
    ].forEach((errorsHandlingMode) => {
        test(`Test successful generation: ${errorsHandlingMode}`, async () => {
            await withMockLLMService(
                async (mockService, basicMockParams, testEventLogger) => {
                    const eventsTracker = subscribeToTrackMockEvents(
                        testEventLogger,
                        mockService,
                        basicMockParams.modelId,
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
                        mockEventsN: 1,
                        successfulRequestEventsN: 1,
                        failedRequestEventsN: 0,
                    });
                    expectLogs([{ status: "SUCCESS" }], mockService);
                }
            );
        });
    });

    async function generateFromChat(
        mockService: MockLLMService,
        mockParams: MockLLMModelParams,
        errorsHandlingMode: ErrorsHandlingMode
    ): Promise<string[]> {
        return mockService.generateFromChat(
            mockChat,
            mockParams,
            proofsToGenerate.length,
            errorsHandlingMode
        );
    }

    testFailedGenerationCompletely(generateFromChat, {
        expectedChatOfMockEvent: mockChat,
        proofsToGenerate: proofsToGenerate,
    });
});
