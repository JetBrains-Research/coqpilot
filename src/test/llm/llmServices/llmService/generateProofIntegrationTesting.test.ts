import { expect } from "earl";

import { ConfigurationError } from "../../../../llm/llmServiceErrors";
import { ErrorsHandlingMode } from "../../../../llm/llmServices/commonStructures/errorsHandlingMode";
import { ProofGenerationMetadataHolder } from "../../../../llm/llmServices/commonStructures/proofGenerationMetadata";

import { EventLogger } from "../../../../logging/eventLogger";
import {
    mockProofGenerationContext,
    proofsToGenerate,
} from "../../llmSpecificTestUtils/constants";
import {
    MockEventsTracker,
    subscribeToTrackMockEvents,
} from "../../llmSpecificTestUtils/eventsTracker";
import { toProofVersion } from "../../llmSpecificTestUtils/expectGeneratedProof";
import {
    ExpectedRecord,
    expectLogs,
} from "../../llmSpecificTestUtils/expectLogs";
import {
    MockLLMGeneratedProof,
    MockLLMModelParams,
    MockLLMService,
} from "../../llmSpecificTestUtils/mockLLMService";
import {
    testFailedGenerationCompletely,
    testFailureAtChatBuilding,
} from "../../llmSpecificTestUtils/testFailedGeneration";
import { expectSuccessfullyGeneratedProofs } from "../../llmSpecificTestUtils/testSuccessfulGeneration";
import { enhanceMockParams } from "../../llmSpecificTestUtils/transformParams";
import { withMockLLMService } from "../../llmSpecificTestUtils/withMockLLMService";

/*
 * Note: fitting context (theorems, diagnostics) into chats is tested in
 * `chatFactory.test.ts` and `chatTokensFitter.test.ts`.
 * Therefore, in this suite testing of context-fitting will be omitted.
 */
suite("[LLMService] Integration testing of `generateProof`", () => {
    test("Test success, 1 round and default settings", async () => {
        await withMockLLMService(
            ErrorsHandlingMode.RETHROW_ERRORS,
            async (mockService, basicMockParams, testEventLogger) => {
                const eventsTracker = subscribeToTrackMockEvents(
                    testEventLogger,
                    mockService,
                    basicMockParams.modelId
                );

                const metadataHolder = new ProofGenerationMetadataHolder();
                const generatedProofs = await mockService.generateProof(
                    mockProofGenerationContext,
                    basicMockParams,
                    proofsToGenerate.length,
                    metadataHolder
                );

                expectSuccessfullyGeneratedProofs(
                    generatedProofs,
                    metadataHolder,
                    {
                        proofsToGenerateNumber: proofsToGenerate.length,
                        getProof: (i) => proofsToGenerate[i],
                        getVersionNumber: () => 1,
                        getProofVersions: (i, rawProofMetadata) => [
                            toProofVersion(
                                proofsToGenerate[i],
                                rawProofMetadata
                            ),
                        ],
                        getCanBeFixed: () => false,
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

    async function generateProof(
        mockService: MockLLMService,
        mockParams: MockLLMModelParams,
        metadataHolder: ProofGenerationMetadataHolder
    ): Promise<string[]> {
        return (
            await mockService.generateProof(
                mockProofGenerationContext,
                mockParams,
                proofsToGenerate.length,
                metadataHolder
            )
        ).map((generatedProof) => generatedProof.proof);
    }

    testFailedGenerationCompletely(generateProof, {
        proofsToGenerate: proofsToGenerate,
    });

    testFailureAtChatBuilding(generateProof, {
        proofsToGenerate: proofsToGenerate,
    });

    test("Test successful 2-round generation, default settings", async () => {
        await withMockLLMService(
            ErrorsHandlingMode.RETHROW_ERRORS,
            async (mockService, basicMockParams, testEventLogger) => {
                const eventsTracker = subscribeToTrackMockEvents(
                    testEventLogger,
                    mockService,
                    basicMockParams.modelId
                );

                const withFixesMockParams = enhanceMockParams(basicMockParams, {
                    maxRoundsNumber: 2,
                    defaultProofFixChoices: 3,

                    // makes MockLLMService generate `Fixed.` proofs if is found in sent chat
                    proofFixPrompt: MockLLMService.proofFixPrompt,
                });

                const generatedProofs = await mockService.generateProof(
                    mockProofGenerationContext,
                    withFixesMockParams,
                    proofsToGenerate.length
                );
                expect(generatedProofs).toHaveLength(proofsToGenerate.length);

                const diagnostic = "Proof is incorrect...";
                for (const generatedProof of generatedProofs) {
                    expect(generatedProof.canBeFixed()).toBeTruthy();
                    const metadataHolder = new ProofGenerationMetadataHolder();
                    const fixedGeneratedProofs = await generatedProof.fixProof(
                        diagnostic,
                        generatedProof.modelParams.multiroundProfile
                            .defaultProofFixChoices,
                        metadataHolder
                    );

                    expectSuccessfullyGeneratedProofs(
                        fixedGeneratedProofs,
                        metadataHolder,
                        {
                            proofsToGenerateNumber:
                                withFixesMockParams.multiroundProfile
                                    .defaultProofFixChoices,
                            getProof: () => MockLLMService.fixedProofString,
                            getVersionNumber: () => 2,
                            getProofVersions: (_, rawProofMetadata) => [
                                toProofVersion(
                                    generatedProof.proof,
                                    generatedProof.rawProof,
                                    diagnostic
                                ),
                                toProofVersion(
                                    MockLLMService.fixedProofString,
                                    rawProofMetadata
                                ),
                            ],
                            getCanBeFixed: () => false,
                        }
                    );
                }

                const generationsN = 1 + generatedProofs.length;
                expect(eventsTracker).toEqual({
                    mockEventsN: generationsN,
                    successfulRequestEventsN: generationsN,
                    failedRequestEventsN: 0,
                });
                expectLogs(
                    new Array(generationsN).fill({ status: "SUCCESS" }),
                    mockService
                );
            }
        );
    });

    test("Stress test with single worker (multiround with random failures, default settings)", async () => {
        await stressTest(
            {
                workersN: 1,
                iterationsPerWorker: 1000,
                newProofsOnEachIteration: 10,
                proofFixChoices: 4,
                tryToFixProbability: 0.5,
                failedGenerationProbability: 0.5,
            },
            true
        );
    }).timeout(40000);

    test("Stress test with async workers (multiround with random failures, default settings)", async () => {
        await stressTest(
            {
                workersN: 10,
                iterationsPerWorker: 100,
                newProofsOnEachIteration: 10,
                proofFixChoices: 4,
                tryToFixProbability: 0.5,
                failedGenerationProbability: 0.5,
            },
            false
        );
    }).timeout(5000);

    interface StressTestParams {
        workersN: number;
        iterationsPerWorker: number;
        newProofsOnEachIteration: number;
        proofFixChoices: number;
        tryToFixProbability: number;
        failedGenerationProbability: number;
    }

    async function stressTest(
        testParams: StressTestParams,
        checkLogsEachIteration: boolean
    ) {
        await withMockLLMService(
            ErrorsHandlingMode.SWALLOW_ERRORS,
            async (mockService, basicMockParams, testEventLogger) => {
                const [actualEvents, expectedEvents, _undefined] =
                    await stressTestImpl(
                        testParams,
                        mockService,
                        basicMockParams,
                        testEventLogger,
                        checkLogsEachIteration
                    );

                expect(actualEvents).toEqual(expectedEvents);

                const logs = mockService.readGenerationsLogs();
                const successLogsN = logs.filter(
                    (record) => record.responseStatus === "SUCCESS"
                ).length;
                const failureLogsN = logs.filter(
                    (record) => record.responseStatus === "FAILURE"
                ).length;
                expect(successLogsN).toEqual(
                    expectedEvents.successfulRequestEventsN
                );
                expect(failureLogsN).toEqual(
                    expectedEvents.failedRequestEventsN
                );
            }
        );
    }

    async function stressTestImpl(
        testParams: StressTestParams,
        mockService: MockLLMService,
        basicMockParams: MockLLMModelParams,
        testEventLogger: EventLogger,
        expectLogsAndCheckExpectations: boolean
    ): Promise<
        [MockEventsTracker, MockEventsTracker, ExpectedRecord[] | undefined]
    > {
        const actualEvents = subscribeToTrackMockEvents(
            testEventLogger,
            mockService,
            basicMockParams.modelId
        );
        const expectedEvents: MockEventsTracker = {
            mockEventsN: 0,
            successfulRequestEventsN: 0,
            failedRequestEventsN: 0,
        };
        const expectedLogs: ExpectedRecord[] | undefined =
            expectLogsAndCheckExpectations ? [] : undefined;

        expect(testParams.newProofsOnEachIteration).toBeLessThanOrEqual(
            basicMockParams.proofsToGenerate.length
        );
        basicMockParams.multiroundProfile.defaultProofFixChoices =
            testParams.proofFixChoices;

        const connectionError = Error("failed to reach server");
        const diagnostic = "Proof is incorrect.";

        const workers: Promise<string>[] = [];
        for (let w = 0; w < testParams.workersN; w++) {
            const work = async () => {
                const workerMockParams: MockLLMModelParams = {
                    ...basicMockParams,
                    workerId: w,
                };

                let toFixCandidates: MockLLMGeneratedProof[] = [];
                for (let i = 0; i < testParams.iterationsPerWorker; i++) {
                    const throwError = throwErrorOnNextGeneration(
                        testParams.failedGenerationProbability,
                        mockService,
                        connectionError,
                        w
                    );
                    const generatedProofs = await mockService.generateProof(
                        mockProofGenerationContext,
                        workerMockParams,
                        testParams.newProofsOnEachIteration
                    );
                    updateExpectations(
                        throwError,
                        generatedProofs,
                        testParams.newProofsOnEachIteration,
                        expectedEvents,
                        expectedLogs
                    );
                    if (expectedLogs !== undefined) {
                        checkExpectations(
                            actualEvents,
                            expectedEvents,
                            expectedLogs,
                            mockService
                        );
                    }

                    toFixCandidates = [toFixCandidates, generatedProofs]
                        .flat()
                        .filter((_generatedProof) => {
                            tossCoin(testParams.tryToFixProbability);
                        });

                    const newlyGeneratedProofs = [];
                    for (const generatedProofToFix of toFixCandidates) {
                        if (!generatedProofToFix.canBeFixed()) {
                            await expect(
                                async () =>
                                    await generatedProofToFix.fixProof(
                                        diagnostic
                                    )
                            ).toBeRejectedWith(
                                ConfigurationError,
                                "could not be fixed"
                            );
                        } else {
                            const throwError = throwErrorOnNextGeneration(
                                testParams.failedGenerationProbability,
                                mockService,
                                connectionError,
                                w
                            );
                            const fixedGeneratedProofs =
                                await generatedProofToFix.fixProof(diagnostic);

                            updateExpectations(
                                throwError,
                                fixedGeneratedProofs,
                                basicMockParams.multiroundProfile
                                    .defaultProofFixChoices,
                                expectedEvents,
                                expectedLogs
                            );
                            if (expectedLogs !== undefined) {
                                checkExpectations(
                                    actualEvents,
                                    expectedEvents,
                                    expectedLogs,
                                    mockService
                                );
                            }
                            newlyGeneratedProofs.push(...fixedGeneratedProofs);
                        }
                    }
                    toFixCandidates = newlyGeneratedProofs;
                }
                return "done";
            };
            workers.push(work());
        }

        const results = await Promise.all(workers);
        expect(results).toEqual(new Array(testParams.workersN).fill("done"));
        return [actualEvents, expectedEvents, expectedLogs];
    }

    function throwErrorOnNextGeneration(
        probability: number,
        mockService: MockLLMService,
        error: Error,
        workerId: number
    ): Error | undefined {
        const coin = tossCoin(probability);
        if (coin) {
            mockService.throwErrorOnNextGeneration(error, workerId);
        }
        return coin ? error : undefined;
    }

    function tossCoin(trueProbability: number): boolean {
        return Math.random() < trueProbability;
    }

    function updateExpectations(
        errorWasThrown: Error | undefined,
        generatedProofs: MockLLMGeneratedProof[],
        expectedProofsLength: number,
        expectedEvents: MockEventsTracker,
        expectedLogs?: ExpectedRecord[]
    ) {
        expectedEvents.mockEventsN += 1;
        if (errorWasThrown !== undefined) {
            expect(generatedProofs).toHaveLength(0);
            expectedEvents.failedRequestEventsN += 1;
            expectedLogs?.push({
                status: "FAILURE",
                error: errorWasThrown,
            });
        } else {
            expect(generatedProofs).toHaveLength(expectedProofsLength);
            expectedEvents.successfulRequestEventsN += 1;
            expectedLogs?.push({ status: "SUCCESS" });
        }
    }

    function checkExpectations(
        actualEvents: MockEventsTracker,
        expectedEvents: MockEventsTracker,
        expectedLogs: ExpectedRecord[],
        mockService: MockLLMService
    ) {
        expect(actualEvents).toEqual(expectedEvents);
        expectLogs(expectedLogs, mockService);
    }
});
