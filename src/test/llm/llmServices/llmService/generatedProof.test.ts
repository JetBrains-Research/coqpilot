import { expect } from "earl";

import { AnalyzedChatHistory } from "../../../../llm/llmServices/chat";
import {
    ErrorsHandlingMode,
    GeneratedProof,
    ProofVersion,
} from "../../../../llm/llmServices/llmService";
import { ProofGenerationContext } from "../../../../llm/proofGenerationContext";

import {
    MockLLMGeneratedProof,
    MockLLMModelParams,
    MockLLMService,
} from "../../testUtils/mockLLMService";
import {
    enhanceMockParams,
    mockChat,
    proofsToGenerate,
    withMockLLMService,
} from "../../testUtils/testGenerateProofPipeline";

/*
 * Note: fitting context (theorems, diagnostics) into chats is tested in
 * `chatFactory.test.ts` and `chatTokensFitter.test.ts`.
 * Therefore, in this suite tesing of context-fitting will be omitted.
 */
suite("[LLMService] Test `GeneratedProof`", () => {
    // the first initial proof and 3 new ones = at least 4 proofs to generate
    expect(proofsToGenerate.length).toBeGreaterThanOrEqual(4);

    const mockProofGenerationContext: ProofGenerationContext = {
        completionTarget: "forall n : nat, 0 + n = n",
        contextTheorems: [],
    };

    function transformChatToSkipProofs(
        analyzedChat: AnalyzedChatHistory,
        mockService: MockLLMService,
        skipFirstNProofs: number
    ): AnalyzedChatHistory {
        return {
            chat: mockService.transformChatToSkipFirstNProofs(
                analyzedChat.chat,
                skipFirstNProofs
            ),
            estimatedTokens: analyzedChat.estimatedTokens,
        };
    }

    interface ExpectedGeneratedProof {
        proof: string;
        versionNumber: number;
        proofVersions: ProofVersion[];
        nextVersionCanBeGenerated?: boolean;
        canBeFixed?: Boolean;
    }

    function expectGeneratedProof(
        actual: GeneratedProof,
        expected: ExpectedGeneratedProof
    ) {
        const mockGeneratedProof = actual as MockLLMGeneratedProof;
        expect(mockGeneratedProof.proof()).toEqual(expected.proof);
        expect(mockGeneratedProof.versionNumber()).toEqual(
            expected.versionNumber
        );
        expect(mockGeneratedProof.proofVersions).toEqual(
            expected.proofVersions
        );
        if (expected.nextVersionCanBeGenerated !== undefined) {
            expect(mockGeneratedProof.nextVersionCanBeGenerated()).toEqual(
                expected.nextVersionCanBeGenerated
            );
        }
        if (expected.canBeFixed !== undefined) {
            expect(mockGeneratedProof.canBeFixed()).toEqual(
                expected.canBeFixed
            );
        }
    }

    function constructInitialGeneratedProof(
        basicMockParams: MockLLMModelParams,
        mockService: MockLLMService
    ): MockLLMGeneratedProof {
        const unlimitedTokensWithFixesMockParams = enhanceMockParams(
            basicMockParams,
            {
                maxRoundsNumber: 2,

                // will be overriden at calls
                proofFixChoices: 1,

                // makes MockLLMService generate `Fixed.` proofs if is found in sent chat
                proofFixPrompt: mockService.proofFixPrompt,
            }
        );
        return mockService.constructGeneratedProof(
            proofsToGenerate[0],
            mockProofGenerationContext,
            unlimitedTokensWithFixesMockParams
        ) as MockLLMGeneratedProof;
    }

    function toProofVersion(
        proof: string,
        diagnostic: string | undefined = undefined
    ): ProofVersion {
        return { proof: proof, diagnostic: diagnostic };
    }

    test("Build initial version", async () => {
        await withMockLLMService(
            async (mockService, basicMockParams, _testEventLogger) => {
                const initialGeneratedProof = constructInitialGeneratedProof(
                    basicMockParams,
                    mockService
                );
                expectGeneratedProof(initialGeneratedProof, {
                    proof: proofsToGenerate[0],
                    versionNumber: 1,
                    proofVersions: [toProofVersion(proofsToGenerate[0])],
                    nextVersionCanBeGenerated: true,
                    canBeFixed: true,
                });
            }
        );
    });

    test("Generate next version", async () => {
        await withMockLLMService(
            async (mockService, basicMockParams, _testEventLogger) => {
                const initialGeneratedProof = constructInitialGeneratedProof(
                    basicMockParams,
                    mockService
                );

                const newVersionChoices = 3;
                const secondVersionGeneratedProofs =
                    await initialGeneratedProof.generateNextVersion(
                        transformChatToSkipProofs(mockChat, mockService, 1),
                        newVersionChoices,
                        ErrorsHandlingMode.RETHROW_ERRORS,
                        (proof) => proof
                    );
                expect(secondVersionGeneratedProofs).toHaveLength(
                    newVersionChoices
                );

                // test that `proofVersions` of the initial proof didn't change
                expect(initialGeneratedProof.proofVersions).toEqual([
                    toProofVersion(proofsToGenerate[0]),
                ]);

                for (let i = 0; i < newVersionChoices; i++) {
                    const expectedNewProof = proofsToGenerate[i + 1];
                    expectGeneratedProof(secondVersionGeneratedProofs[i], {
                        proof: expectedNewProof,
                        versionNumber: 2,
                        proofVersions: [
                            toProofVersion(proofsToGenerate[0]),
                            toProofVersion(expectedNewProof),
                        ],
                        nextVersionCanBeGenerated: false, // `maxRoundsNumber`: 2
                    });
                }
            }
        );
    });

    test("Fix proof", async () => {
        await withMockLLMService(
            async (mockService, basicMockParams, _testEventLogger) => {
                const initialGeneratedProof = constructInitialGeneratedProof(
                    basicMockParams,
                    mockService
                );

                const fixedVersionChoices = 3;
                const initialProofDiagnostic = `Proof \`${initialGeneratedProof.proof()}\` was incorrect...`;
                const fixedGeneratedProofs =
                    await initialGeneratedProof.fixProof(
                        initialProofDiagnostic,
                        fixedVersionChoices,
                        ErrorsHandlingMode.RETHROW_ERRORS
                    );
                expect(fixedGeneratedProofs).toHaveLength(fixedVersionChoices);

                // test that `proofVersions` of the initial proof was updated correctly
                expect(initialGeneratedProof.proofVersions).toEqual([
                    toProofVersion(proofsToGenerate[0], initialProofDiagnostic),
                ]);

                const expectedFixedProof = mockService.fixedProofString;
                fixedGeneratedProofs.forEach((fixedGeneratedProof) => {
                    expectGeneratedProof(fixedGeneratedProof, {
                        proof: expectedFixedProof,
                        versionNumber: 2,
                        proofVersions: [
                            toProofVersion(
                                proofsToGenerate[0],
                                initialProofDiagnostic
                            ),
                            toProofVersion(expectedFixedProof),
                        ],
                        canBeFixed: false,
                    });
                });
            }
        );
    });
});
