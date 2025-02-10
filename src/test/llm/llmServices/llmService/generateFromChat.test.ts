import { expect } from "earl";

import { ErrorsHandlingMode } from "../../../../llm/llmServices/commonStructures/errorsHandlingMode";
import { ProofGenerationMetadataHolder } from "../../../../llm/llmServices/commonStructures/proofGenerationMetadata";

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
import { expectSuccessfullyGeneratedItems } from "../../llmSpecificTestUtils/testSuccessfulGeneration";
import { withMockLLMService } from "../../llmSpecificTestUtils/withMockLLMService";

suite("[LLMService] Test `generateFromChat`", () => {
    [
        ErrorsHandlingMode.SWALLOW_ERRORS,
        ErrorsHandlingMode.RETHROW_ERRORS,
    ].forEach((errorsHandlingMode) => {
        test(`Test successful generation: ${errorsHandlingMode}`, async () => {
            await withMockLLMService(
                ErrorsHandlingMode.RETHROW_ERRORS,
                async (mockService, basicMockParams, testEventLogger) => {
                    const eventsTracker = subscribeToTrackMockEvents(
                        testEventLogger,
                        mockService,
                        basicMockParams.modelId,
                        mockChat
                    );

                    const metadataHolder = new ProofGenerationMetadataHolder();
                    const generatedProofs = await mockService.generateFromChat(
                        mockChat,
                        basicMockParams,
                        proofsToGenerate.length,
                        metadataHolder
                    );
                    expectSuccessfullyGeneratedItems(
                        generatedProofs,
                        metadataHolder,
                        proofsToGenerate.length,
                        (i) => proofsToGenerate[i],
                        (proof, rawProofMetadata, _, expectedProof) => {
                            expect(proof).toEqual(expectedProof);
                            expect(proof).toEqual(rawProofMetadata.content);
                        }
                    );

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
        metadataHolder: ProofGenerationMetadataHolder
    ): Promise<string[]> {
        return mockService.generateFromChat(
            mockChat,
            mockParams,
            proofsToGenerate.length,
            metadataHolder
        );
    }

    testFailedGenerationCompletely(generateFromChat, {
        expectedChatOfMockEvent: mockChat,
        proofsToGenerate: proofsToGenerate,
    });
});
