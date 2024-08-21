import { expect } from "earl";

import { AnalyzedChatHistory } from "../../../../llm/llmServices/chat";
import { ErrorsHandlingMode } from "../../../../llm/llmServices/llmService";

import {
    mockChat,
    mockProofGenerationContext,
    proofsToGenerate,
} from "../../llmSpecificTestUtils/constants";
import {
    expectGeneratedProof,
    toProofVersion,
} from "../../llmSpecificTestUtils/expectGeneratedProof";
import {
    MockLLMGeneratedProof,
    MockLLMModelParams,
    MockLLMService,
} from "../../llmSpecificTestUtils/mockLLMService";
import { testFailedGenerationCompletely } from "../../llmSpecificTestUtils/testFailedGeneration";
import { enhanceMockParams } from "../../llmSpecificTestUtils/transformParams";
import { withMockLLMService } from "../../llmSpecificTestUtils/withMockLLMService";

/*
 * Note: fitting context (theorems, diagnostics) into chats is tested in
 * `chatFactory.test.ts` and `chatTokensFitter.test.ts`.
 * Therefore, in this suite testing of context-fitting will be omitted.
 */
suite("[LLMService] Test `GeneratedProof`", () => {
    // the first initial proof and 3 new ones = at least 4 proofs to generate
    expect(proofsToGenerate.length).toBeGreaterThanOrEqual(4);

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
            contextTheorems: analyzedChat.contextTheorems,
            estimatedTokens: analyzedChat.estimatedTokens,
        };
    }

    async function constructInitialGeneratedProof(
        mockService: MockLLMService,
        basicMockParams: MockLLMModelParams
    ): Promise<MockLLMGeneratedProof> {
        const unlimitedTokensWithFixesMockParams = enhanceMockParams(
            basicMockParams,
            {
                maxRoundsNumber: 2,

                // will be overriden at calls
                defaultProofFixChoices: 1,

                // makes MockLLMService generate `Fixed.` proofs if is found in sent chat
                proofFixPrompt: MockLLMService.proofFixPrompt,
            }
        );
        const generatedProofs = await mockService.generateProof(
            mockProofGenerationContext,
            unlimitedTokensWithFixesMockParams,
            1,
            ErrorsHandlingMode.RETHROW_ERRORS
        );
        expect(generatedProofs).toHaveLength(1);
        return generatedProofs[0] as MockLLMGeneratedProof;
    }

    test("Build initial version", async () => {
        await withMockLLMService(
            async (mockService, basicMockParams, _testEventLogger) => {
                const initialGeneratedProof =
                    await constructInitialGeneratedProof(
                        mockService,
                        basicMockParams
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

    async function testExtractsProof(
        dirtyProof: string,
        expectedExtractedProof: string
    ): Promise<void> {
        return withMockLLMService(
            async (mockService, basicMockParams, _testEventLogger) => {
                const generatedProof = await constructInitialGeneratedProof(
                    mockService,
                    {
                        ...basicMockParams,
                        proofsToGenerate: [dirtyProof],
                    }
                );
                expectGeneratedProof(generatedProof, {
                    proof: expectedExtractedProof,
                    versionNumber: 1,
                    proofVersions: [toProofVersion(expectedExtractedProof)],
                });
            }
        );
    }

    test("Correctly extracts proof from dirty input (when created)", async () => {
        await testExtractsProof("auto.", "auto.");
        await testExtractsProof("Proof. auto.", "Proof. auto.");
        await testExtractsProof("auto. Qed.", "auto. Qed.");
        await testExtractsProof("some text", "some text");

        await testExtractsProof("Proof.auto.Qed.", "auto.");
        await testExtractsProof("Proof.Qed.", "");

        await testExtractsProof("Proof. auto. Qed.", "auto.");
        await testExtractsProof("Proof.\nauto.\nQed.", "auto.");
        await testExtractsProof("Proof.\n\tauto.\nQed.", "auto.");
        await testExtractsProof("\tProof.\n\t\tauto.\n\tQed.", "auto.");

        await testExtractsProof("PrefixProof.auto.Qed.Suffix", "auto.");
        await testExtractsProof(
            "The following proof should solve your theorem:\n```Proof.\n\tauto.\nQed.```\nAsk me more questions, if you want to!",
            "auto."
        );

        await testExtractsProof("Proof.auto.Qed. Proof.intros.Qed.", "auto.");
    });

    test("Mock multiround: generate next version, happy path", async () => {
        await withMockLLMService(
            async (mockService, basicMockParams, _testEventLogger) => {
                const initialGeneratedProof =
                    await constructInitialGeneratedProof(
                        mockService,
                        basicMockParams
                    );

                const newVersionChoices = 3;
                const secondVersionGeneratedProofs =
                    await initialGeneratedProof.generateNextVersion(
                        transformChatToSkipProofs(mockChat, mockService, 1),
                        newVersionChoices,
                        ErrorsHandlingMode.RETHROW_ERRORS
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

    test("Fix proof, happy path", async () => {
        await withMockLLMService(
            async (mockService, basicMockParams, _testEventLogger) => {
                const initialGeneratedProof =
                    await constructInitialGeneratedProof(
                        mockService,
                        basicMockParams
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

                const expectedFixedProof = MockLLMService.fixedProofString;
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

    async function fixProof(
        _mockService: MockLLMService,
        _mockParams: MockLLMModelParams,
        errorsHandlingMode: ErrorsHandlingMode,
        preparedData?: MockLLMGeneratedProof
    ): Promise<string[]> {
        const initialGeneratedProof = preparedData;
        if (initialGeneratedProof === undefined) {
            throw Error(
                `test is configured incorrectly: \`fixProof\` got "undefined" as \`preparedData\` instead of \`MockLLMGeneratedProof\``
            );
        }
        const fixedGeneratedProofs = await initialGeneratedProof.fixProof(
            "Proof was incorrect",
            1,
            errorsHandlingMode
        );

        return fixedGeneratedProofs.map((generatedProof) =>
            generatedProof.proof()
        );
    }

    async function prepareData(
        mockService: MockLLMService,
        basicMockParams: MockLLMModelParams
    ): Promise<MockLLMGeneratedProof> {
        const initialGeneratedProof = await constructInitialGeneratedProof(
            mockService,
            basicMockParams
        );
        mockService.clearGenerationLogs();
        return initialGeneratedProof;
    }

    testFailedGenerationCompletely(
        fixProof,
        {
            proofsToGenerate: [MockLLMService.fixedProofString],
            testTargetName: "Fix proof, failed generation",
        },
        prepareData
    );
});
