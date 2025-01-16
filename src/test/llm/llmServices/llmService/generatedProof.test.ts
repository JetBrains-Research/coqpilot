import { expect } from "earl";

import { AnalyzedChatHistory } from "../../../../llm/llmServices/commonStructures/chat";
import { ErrorsHandlingMode } from "../../../../llm/llmServices/commonStructures/errorsHandlingMode";
import { GeneratedRawContentItem } from "../../../../llm/llmServices/commonStructures/generatedRawContent";
import { ProofGenerationMetadataHolder } from "../../../../llm/llmServices/commonStructures/proofGenerationMetadata";

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
import { expectSuccessfullyGeneratedProofs } from "../../llmSpecificTestUtils/testSuccessfulGeneration";
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

    interface ConstructedProof {
        generatedProof: MockLLMGeneratedProof;
        rawProofMetadata: GeneratedRawContentItem;
    }

    async function constructInitialGeneratedProof(
        mockService: MockLLMService,
        basicMockParams: MockLLMModelParams
    ): Promise<ConstructedProof> {
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
        const metadataHolder = new ProofGenerationMetadataHolder();
        const generatedProofs = await mockService.generateProof(
            mockProofGenerationContext,
            unlimitedTokensWithFixesMockParams,
            1,
            metadataHolder
        );
        const successMetadata =
            metadataHolder.getSuccessfulProofGenerationMetadata();

        expect(generatedProofs).toHaveLength(1);
        expect(successMetadata.generatedRawProofs).toHaveLength(1);
        return {
            generatedProof: generatedProofs[0],
            rawProofMetadata: successMetadata.generatedRawProofs[0],
        };
    }

    test("Build initial version", async () => {
        await withMockLLMService(
            ErrorsHandlingMode.RETHROW_ERRORS,
            async (mockService, basicMockParams) => {
                const { generatedProof, rawProofMetadata } =
                    await constructInitialGeneratedProof(
                        mockService,
                        basicMockParams
                    );
                expectGeneratedProof(generatedProof, {
                    proof: proofsToGenerate[0],
                    versionNumber: 1,
                    rawProofMetadata: rawProofMetadata,
                    proofVersions: [
                        toProofVersion(proofsToGenerate[0], rawProofMetadata),
                    ],
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
            ErrorsHandlingMode.RETHROW_ERRORS,
            async (mockService, basicMockParams) => {
                const { generatedProof, rawProofMetadata } =
                    await constructInitialGeneratedProof(mockService, {
                        ...basicMockParams,
                        proofsToGenerate: [dirtyProof],
                    });
                expect(rawProofMetadata.content).toEqual(dirtyProof);
                expectGeneratedProof(generatedProof, {
                    proof: expectedExtractedProof,
                    versionNumber: 1,
                    rawProofMetadata: rawProofMetadata,
                    proofVersions: [
                        toProofVersion(
                            expectedExtractedProof,
                            rawProofMetadata
                        ),
                    ],
                });
            }
        );
    }

    test("Correctly extracts proof from dirty input (when created)", async () => {
        await testExtractsProof("auto.", "auto.");
        await testExtractsProof("Proof. auto.", " auto.");
        await testExtractsProof("auto. Qed.", "auto. ");
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

    test("Correctly extracts proof from LLaMA with 'Proof using' and similar inputs", async () => {
        await testExtractsProof(
            "Proof. intros.\nreflexivity. Qed.",
            "intros.\nreflexivity."
        );
        await testExtractsProof(
            "Proof using. intros.\nreflexivity. Qed.",
            "intros.\nreflexivity."
        );
        await testExtractsProof(
            "Proof using HW. intros.\nreflexivity. Qed.",
            "intros.\nreflexivity."
        );
        await testExtractsProof(
            "Proof using HW.intros.\nreflexivity. Qed.",
            "intros.\nreflexivity."
        );
        await testExtractsProof(
            "Proof using HW WB HH CH. intros.\nreflexivity. Qed.",
            "intros.\nreflexivity."
        );
        await testExtractsProof(
            "Proof using HW WB HH CH. intros.\nreflexivity. Abort.",
            "intros.\nreflexivity."
        );
        await testExtractsProof(
            "Proof using. intros.\nreflexivity. Admitted.",
            "intros.\nreflexivity."
        );
        await testExtractsProof(
            "Proof using. intros.\nreflexivity. Defined.",
            "intros.\nreflexivity."
        );
        await testExtractsProof(
            "Proof using. intros.\nreflexivity. Qed. # I wanted to add a comment here\nQed.",
            "intros.\nreflexivity."
        );
    });

    test("Mock multiround: generate next version, happy path", async () => {
        await withMockLLMService(
            ErrorsHandlingMode.RETHROW_ERRORS,
            async (mockService, basicMockParams) => {
                const {
                    generatedProof: parentProof,
                    rawProofMetadata: parentProofMetadata,
                } = await constructInitialGeneratedProof(
                    mockService,
                    basicMockParams
                );

                const newVersionChoices = 3;
                const secondRoundMetadataHolder =
                    new ProofGenerationMetadataHolder();
                const secondRoundGeneratedProofs =
                    await parentProof.generateNextVersion(
                        transformChatToSkipProofs(mockChat, mockService, 1),
                        newVersionChoices,
                        secondRoundMetadataHolder
                    );

                // test that `proofVersions` of the initial proof didn't change
                expect(parentProof.proofVersions).toEqual([
                    toProofVersion(proofsToGenerate[0], parentProofMetadata),
                ]);

                expectSuccessfullyGeneratedProofs(
                    secondRoundGeneratedProofs,
                    secondRoundMetadataHolder,
                    {
                        proofsToGenerateNumber: newVersionChoices,
                        getProof: (i) => proofsToGenerate[i + 1],
                        getVersionNumber: () => 2,
                        getProofVersions: (i, rawProofMetadata) => [
                            toProofVersion(
                                proofsToGenerate[0],
                                parentProofMetadata
                            ),
                            toProofVersion(
                                proofsToGenerate[i + 1],
                                rawProofMetadata
                            ),
                        ],
                        getCanBeFixed: () => false, // `maxRoundsNumber`: 2
                    }
                );
            }
        );
    });

    test("Fix proof, happy path", async () => {
        await withMockLLMService(
            ErrorsHandlingMode.RETHROW_ERRORS,
            async (mockService, basicMockParams, _) => {
                const {
                    generatedProof: parentProof,
                    rawProofMetadata: parentProofMetadata,
                } = await constructInitialGeneratedProof(
                    mockService,
                    basicMockParams
                );

                const fixedVersionChoices = 3;
                const initialProofDiagnostic = `Proof \`${parentProof.proof}\` was incorrect...`;
                const secondRoundMetadataHolder =
                    new ProofGenerationMetadataHolder();
                const fixedGeneratedProofs = await parentProof.fixProof(
                    initialProofDiagnostic,
                    fixedVersionChoices,
                    secondRoundMetadataHolder
                );

                // test that `proofVersions` of the initial proof is updated correctly
                expect(parentProof.proofVersions).toEqual([
                    toProofVersion(
                        proofsToGenerate[0],
                        parentProofMetadata,
                        initialProofDiagnostic
                    ),
                ]);

                const expectedFixedProof = MockLLMService.fixedProofString;
                expectSuccessfullyGeneratedProofs(
                    fixedGeneratedProofs,
                    secondRoundMetadataHolder,
                    {
                        proofsToGenerateNumber: fixedVersionChoices,
                        getProof: () => expectedFixedProof,
                        getVersionNumber: () => 2,
                        getProofVersions: (_, rawProofMetadata) => [
                            toProofVersion(
                                proofsToGenerate[0],
                                parentProofMetadata,
                                initialProofDiagnostic
                            ),
                            toProofVersion(
                                expectedFixedProof,
                                rawProofMetadata
                            ),
                        ],
                        getCanBeFixed: () => false,
                    }
                );
            }
        );
    });

    async function fixProof(
        _mockService: MockLLMService,
        _mockParams: MockLLMModelParams,
        metadataHolder: ProofGenerationMetadataHolder,
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
            metadataHolder
        );

        return fixedGeneratedProofs.map(
            (generatedProof) => generatedProof.proof
        );
    }

    async function prepareData(
        mockService: MockLLMService,
        basicMockParams: MockLLMModelParams
    ): Promise<MockLLMGeneratedProof> {
        const constructedProof = await constructInitialGeneratedProof(
            mockService,
            basicMockParams
        );
        mockService.clearGenerationLogs();
        return constructedProof.generatedProof;
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
