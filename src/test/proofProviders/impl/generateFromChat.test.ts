import { expect } from "earl";

import { ErrorsHandlingMode } from "../../../proofProviders/impl/commonStructures/errorsHandlingMode";
import { ProofGenerationMetadataHolder } from "../../../proofProviders/impl/commonStructures/proofGenerationMetadata";

import {
    mockChat,
    proofsToGenerate,
} from "../proofProvidersSpecificTestUtils/constants";
import { subscribeToTrackMockEvents } from "../proofProvidersSpecificTestUtils/eventsTracker";
import { expectLogs } from "../proofProvidersSpecificTestUtils/expectLogs";
import {
    MockService,
    MockServiceModelParams,
} from "../proofProvidersSpecificTestUtils/mockService";
import { testFailedGenerationCompletely } from "../proofProvidersSpecificTestUtils/testFailedGeneration";
import { expectSuccessfullyGeneratedItems } from "../proofProvidersSpecificTestUtils/testSuccessfulGeneration";
import { withMockService } from "../proofProvidersSpecificTestUtils/withMockService";

suite("[ProofProvider] Test `generateFromChat`", () => {
    [
        ErrorsHandlingMode.SWALLOW_ERRORS,
        ErrorsHandlingMode.RETHROW_ERRORS,
    ].forEach((errorsHandlingMode) => {
        test(`Test successful generation: ${errorsHandlingMode}`, async () => {
            await withMockService(
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
        mockService: MockService,
        mockParams: MockServiceModelParams,
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
