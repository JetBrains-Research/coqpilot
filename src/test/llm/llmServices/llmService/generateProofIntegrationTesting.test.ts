import { expect } from "earl";

import { GeneratedProof } from "../../../../llm/llmServices/llmService";

import { MockLLMService } from "../../testUtils/mockLLMService";
import {
    EventsTracker,
    ExpectedRecord,
    enhanceMockParams,
    expectGeneratedProof,
    expectLogs,
    mockProofGenerationContext,
    proofsToGenerate,
    subscribeToTrackEvents,
    toProofVersion,
    withMockLLMService,
} from "../../testUtils/testGenerateProofPipeline";

/*
 * Note:
 * - fitting context (theorems, diagnostics) into chats is tested in
 * `chatFactory.test.ts` and `chatTokensFitter.test.ts`;
 * - handling of different `ErrorsHandlingMode`-s is tested in `generateFromChat.test.ts`.
 * Therefore, in this suite testing of these items will be omitted.
 */
suite("[LLMService] Integration testing of `generateProof`", () => {
    test("Test success, 1 round and default settings", async () => {
        await withMockLLMService(
            async (mockService, basicMockParams, testEventLogger) => {
                const eventsTracker = subscribeToTrackEvents(
                    testEventLogger,
                    mockService
                );

                const generatedProofs = await mockService.generateProof(
                    mockProofGenerationContext,
                    basicMockParams,
                    proofsToGenerate.length
                );

                expect(generatedProofs).toHaveLength(proofsToGenerate.length);
                for (let i = 0; i < generatedProofs.length; i++) {
                    expectGeneratedProof(generatedProofs[i], {
                        proof: proofsToGenerate[i],
                        proofVersions: [toProofVersion(proofsToGenerate[i])],
                        versionNumber: 1,
                        canBeFixed: false,
                    });
                }

                expect(eventsTracker).toEqual({
                    mockGenerationEventsN: 1,
                    successfulGenerationEventsN: 1,
                    failedGenerationEventsN: 0,
                });
                expectLogs([{ status: "SUCCESS" }], mockService);
            }
        );
    });

    test("Test failure, default error handling", async () => {
        await withMockLLMService(
            async (mockService, basicMockParams, testEventLogger) => {
                const eventsTracker = subscribeToTrackEvents(
                    testEventLogger,
                    mockService
                );

                const connectionError = Error("failed to reach server");
                mockService.throwErrorOnNextGeneration = connectionError;
                const noGeneratedProofs = await mockService.generateProof(
                    mockProofGenerationContext,
                    basicMockParams,
                    proofsToGenerate.length
                );
                expect(noGeneratedProofs).toHaveLength(0);

                expect(eventsTracker).toEqual({
                    mockGenerationEventsN: 1,
                    successfulGenerationEventsN: 0,
                    failedGenerationEventsN: 1,
                });
                const failureRecord: ExpectedRecord = {
                    status: "FAILED",
                    error: connectionError,
                };
                expectLogs([failureRecord], mockService);
            }
        );
    });

    test("Test successful 2-round generation, default settings", async () => {
        await withMockLLMService(
            async (mockService, basicMockParams, testEventLogger) => {
                const eventsTracker = subscribeToTrackEvents(
                    testEventLogger,
                    mockService
                );

                const withFixesMockParams = enhanceMockParams(basicMockParams, {
                    maxRoundsNumber: 2,
                    proofFixChoices: 3,

                    // makes MockLLMService generate `Fixed.` proofs if is found in sent chat
                    proofFixPrompt: mockService.proofFixPrompt,
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
                    const fixedGeneratedProofs =
                        await generatedProof.fixProof(diagnostic);
                    expect(fixedGeneratedProofs).toHaveLength(
                        withFixesMockParams.multiroundProfile.proofFixChoices
                    );

                    fixedGeneratedProofs.forEach((fixedGeneratedProof) => {
                        expectGeneratedProof(fixedGeneratedProof, {
                            proof: mockService.fixedProofString,
                            proofVersions: [
                                toProofVersion(
                                    generatedProof.proof(),
                                    diagnostic
                                ),
                                toProofVersion(mockService.fixedProofString),
                            ],
                            versionNumber: 2,
                            canBeFixed: false,
                        });
                    });
                }

                const generationsN = 1 + generatedProofs.length;
                expect(eventsTracker).toEqual({
                    mockGenerationEventsN: generationsN,
                    successfulGenerationEventsN: generationsN,
                    failedGenerationEventsN: 0,
                });
                expectLogs(
                    new Array(generationsN).fill({ status: "SUCCESS" }),
                    mockService
                );
            }
        );
    });

    function tossCoin(trueProbability: number): boolean {
        return Math.random() < trueProbability;
    }

    function throwErrorOnNextGeneration(
        probability: number,
        mockService: MockLLMService,
        error: Error
    ): Error | undefined {
        const coin = tossCoin(probability);
        mockService.throwErrorOnNextGeneration = coin ? error : undefined;
        return coin ? error : undefined;
    }

    function updateExpectations(
        errorWasThrown: Error | undefined,
        generatedProofs: GeneratedProof[],
        expectedProofsLength: number,
        expectedEvents: EventsTracker,
        expectedLogs: ExpectedRecord[]
    ) {
        expectedEvents.mockGenerationEventsN += 1;
        if (errorWasThrown !== undefined) {
            expect(generatedProofs).toHaveLength(0);
            expectedEvents.failedGenerationEventsN += 1;
            expectedLogs.push({
                status: "FAILED",
                error: errorWasThrown,
            });
        } else {
            expect(generatedProofs).toHaveLength(expectedProofsLength);
            expectedEvents.successfulGenerationEventsN += 1;
            expectedLogs.push({ status: "SUCCESS" });
        }
    }

    function checkExpectations(
        eventsTracker: EventsTracker,
        expectedEvents: EventsTracker,
        expectedLogs: ExpectedRecord[],
        mockService: MockLLMService
    ) {
        expect(eventsTracker).toEqual(expectedEvents);
        expectLogs(expectedLogs, mockService);
    }

    function updateAndCheckExpectations(
        errorWasThrown: Error | undefined,
        generatedProofs: GeneratedProof[],
        expectedProofsLength: number,
        expectedEvents: EventsTracker,
        expectedLogs: ExpectedRecord[],
        eventsTracker: EventsTracker,
        mockService: MockLLMService
    ) {
        updateExpectations(
            errorWasThrown,
            generatedProofs,
            expectedProofsLength,
            expectedEvents,
            expectedLogs
        );
        checkExpectations(
            eventsTracker,
            expectedEvents,
            expectedLogs,
            mockService
        );
    }

    test("Stress test: multiround with random failures, default settings", async () => {
        await withMockLLMService(
            async (mockService, basicMockParams, testEventLogger) => {
                const eventsTracker = subscribeToTrackEvents(
                    testEventLogger,
                    mockService
                );
                const expectedEvents: EventsTracker = {
                    mockGenerationEventsN: 0,
                    successfulGenerationEventsN: 0,
                    failedGenerationEventsN: 0,
                };
                const expectedLogs: ExpectedRecord[] = [];

                const iterations = 1000;
                const newProofsOnEachIteration = 10;
                expect(newProofsOnEachIteration).toBeLessThanOrEqual(
                    basicMockParams.proofsToGenerate.length
                );
                basicMockParams.multiroundProfile.proofFixChoices = 4;

                const tryToFixProbability = 0.5;
                const failedGenerationProbability = 0.5;

                const connectionError = Error("failed to reach server");
                const diagnostic = "Proof is incorrect.";
                let toFixCandidates: GeneratedProof[] = [];

                for (let i = 0; i < iterations; i++) {
                    const throwError = throwErrorOnNextGeneration(
                        failedGenerationProbability,
                        mockService,
                        connectionError
                    );
                    const generatedProofs = await mockService.generateProof(
                        mockProofGenerationContext,
                        basicMockParams,
                        newProofsOnEachIteration
                    );
                    updateAndCheckExpectations(
                        throwError,
                        generatedProofs,
                        newProofsOnEachIteration,
                        expectedEvents,
                        expectedLogs,
                        eventsTracker,
                        mockService
                    );

                    toFixCandidates = [toFixCandidates, generatedProofs]
                        .flat()
                        .filter((_generatedProof) => {
                            tossCoin(tryToFixProbability);
                        });

                    const newlyGeneratedProofs = [];
                    for (const generatedProofToFix of toFixCandidates) {
                        if (!generatedProofToFix.canBeFixed()) {
                            expect(
                                async () =>
                                    await generatedProofToFix.fixProof(
                                        diagnostic
                                    )
                            ).toThrow();
                        } else {
                            const throwError = throwErrorOnNextGeneration(
                                failedGenerationProbability,
                                mockService,
                                connectionError
                            );
                            const fixedGeneratedProofs =
                                await generatedProofToFix.fixProof(diagnostic);

                            updateAndCheckExpectations(
                                throwError,
                                fixedGeneratedProofs,
                                basicMockParams.multiroundProfile
                                    .proofFixChoices,
                                expectedEvents,
                                expectedLogs,
                                eventsTracker,
                                mockService
                            );
                            newlyGeneratedProofs.push(...fixedGeneratedProofs);
                        }
                    }
                    toFixCandidates = newlyGeneratedProofs;
                }
            }
        );
    }).timeout(10000);
});
