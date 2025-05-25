import { expect } from "earl";

import { ErrorsHandlingMode } from "../../../../proofProviders/impl/commonStructures/errorsHandlingMode";
import { ProofGenerationMetadataHolder } from "../../../../proofProviders/impl/commonStructures/proofGenerationMetadata";
import { PredefinedProofsModelParams } from "../../../../proofProviders/impl/modelParams";
import { PredefinedProofsProvider } from "../../../../proofProviders/impl/predefinedProofs/predefinedProofsProvider";
import { resolveParametersOrThrow } from "../../../../proofProviders/impl/utils/resolveOrThrow";
import { ProofGenerationContext } from "../../../../proofProviders/proofGenerationContext";
import { ConfigurationError } from "../../../../proofProviders/proofProviderErrors";
import { PredefinedProofsUserModelParams } from "../../../../proofProviders/userModelParams";

import { EventLogger } from "../../../../logging/eventLogger";
import { delay } from "../../../../utils/async/delay";
import { throwError } from "../../../../utils/errors/throwErrors";
import { timeZero } from "../../../../utils/time";
import { withProofProvider } from "../../../commonTestFunctions/withProofProvider";
import { testModelId } from "../../proofProvidersSpecificTestUtils/constants";
import {
    EventsTracker,
    subscribeToTrackEvents,
} from "../../proofProvidersSpecificTestUtils/eventsTracker";
import { expectLogs } from "../../proofProvidersSpecificTestUtils/expectLogs";
import { testProofProviderCompletesAdmitFromFile } from "../../proofProvidersSpecificTestUtils/testProofProviderInEnvironment";
import {
    testResolveParametersFailsWithSingleCause,
    testResolveValidCompleteParameters,
} from "../../proofProvidersSpecificTestUtils/testResolveParameters";

suite("[ProofProvider] Test `PredefinedProofsProvider`", function () {
    const simpleTactics = ["auto.", "intros.", "reflexivity."];
    const inputParams: PredefinedProofsUserModelParams = {
        modelId: testModelId,
        tactics: simpleTactics,
    };
    const proofGenerationContext: ProofGenerationContext = {
        completionTarget: "could be anything",
        contextTheorems: [],
    };

    async function withPredefinedProofsProvider(
        errorsHandlingMode: ErrorsHandlingMode,
        block: (
            predefinedProofsProvider: PredefinedProofsProvider,
            testEventLogger: EventLogger
        ) => Promise<void>
    ) {
        const testEventLogger = new EventLogger();
        return withProofProvider(
            new PredefinedProofsProvider({
                eventLogger: testEventLogger,
                errorsHandlingMode: errorsHandlingMode,
                debugLogs: true,
            }),
            async (predefinedProofsProvider) => {
                return block(predefinedProofsProvider, testEventLogger);
            }
        );
    }

    async function withDefaultPredefinedProofsProvider(
        block: (
            predefinedProofsProvider: PredefinedProofsProvider,
            testEventLogger: EventLogger
        ) => Promise<void>
    ) {
        return withPredefinedProofsProvider(
            ErrorsHandlingMode.RETHROW_ERRORS,
            block
        );
    }

    const choices = simpleTactics.length;
    const inputFile = ["small_document.v"];

    test("Simple generation: prove with `auto.`", async () => {
        const predefinedProofsProvider = new PredefinedProofsProvider();
        await testProofProviderCompletesAdmitFromFile(
            predefinedProofsProvider,
            inputParams,
            inputFile,
            choices
        );
    });

    [
        ErrorsHandlingMode.SWALLOW_ERRORS,
        ErrorsHandlingMode.RETHROW_ERRORS,
    ].forEach((errorsHandlingMode) => {
        test(`Test generation logging: ${errorsHandlingMode}`, async () => {
            await withPredefinedProofsProvider(
                errorsHandlingMode,
                async (predefinedProofsProvider, testEventLogger) => {
                    const eventsTracker = subscribeToTrackEvents(
                        testEventLogger,
                        predefinedProofsProvider,
                        inputParams.modelId
                    );
                    const resolvedParams = resolveParametersOrThrow(
                        predefinedProofsProvider,
                        inputParams
                    );

                    // failed generation
                    const failedMetadataHolder =
                        new ProofGenerationMetadataHolder();
                    try {
                        await predefinedProofsProvider.generateProof(
                            proofGenerationContext,
                            resolvedParams,
                            resolvedParams.tactics.length + 1,
                            failedMetadataHolder
                        );
                        expect(errorsHandlingMode).toEqual(
                            ErrorsHandlingMode.SWALLOW_ERRORS
                        );
                    } catch (e) {
                        expect(errorsHandlingMode).toEqual(
                            ErrorsHandlingMode.RETHROW_ERRORS
                        );
                        expect(e instanceof ConfigurationError).toBeTruthy();
                    }
                    const failedMetadata =
                        failedMetadataHolder.getFailedProofGenerationMetadata();
                    expect(failedMetadata.analyzedChat).toBeNullish();
                    expect(
                        failedMetadata.proofProviderError instanceof
                            ConfigurationError
                    ).toBeTruthy();

                    const expectedEvents: EventsTracker = {
                        successfulRequestEventsN: 0,
                        failedRequestEventsN: 1,
                    };
                    expect(eventsTracker).toEqual(expectedEvents);

                    // `ConfigurationError` should not be logged!
                    expectLogs([], predefinedProofsProvider);

                    // successful generation
                    const generatedProofs =
                        await predefinedProofsProvider.generateProof(
                            proofGenerationContext,
                            resolvedParams,
                            resolvedParams.tactics.length
                        );
                    expect(generatedProofs).toHaveLength(
                        resolvedParams.tactics.length
                    );

                    expectedEvents.successfulRequestEventsN += 1;
                    expect(eventsTracker).toEqual(expectedEvents);
                    expectLogs(
                        [{ status: "SUCCESS" }],
                        predefinedProofsProvider
                    );
                }
            );
        });
    });

    test("Test `resolveParameters` reads & accepts valid params", async () => {
        await withDefaultPredefinedProofsProvider(
            async (predefinedProofsProvider) => {
                testResolveValidCompleteParameters(
                    predefinedProofsProvider,
                    inputParams
                );
            }
        );
    });

    test("Test `resolveParameters` validates PredefinedProofs-extended params (`tactics`)", async () => {
        await withDefaultPredefinedProofsProvider(
            async (predefinedProofsProvider) => {
                testResolveParametersFailsWithSingleCause(
                    predefinedProofsProvider,
                    {
                        ...inputParams,
                        tactics: [],
                    },
                    "tactics"
                );
            }
        );
    });

    test("Test `resolveParameters` overrides params correctly", async () => {
        await withDefaultPredefinedProofsProvider(
            async (predefinedProofsProvider) => {
                const resolutionResult =
                    predefinedProofsProvider.resolveParameters({
                        ...inputParams,
                        choices: 1,
                        systemPrompt: "asking for something",
                        maxTokensToGenerate: 2000,
                        tokensLimit: 4000,
                        maxContextTheoremsNumber: 20,
                        multiroundProfile: {
                            maxRoundsNumber: 10,
                            proofFixChoices: 5,
                            proofFixPrompt: "asking for more of something",
                            maxPreviousProofVersionsNumber: 2,
                        },
                    });

                // first, verify all params were read correctly
                for (const paramLog of resolutionResult.resolutionLogs) {
                    expect(paramLog.isInvalidCause).toBeNullish();
                    expect(
                        paramLog.inputReadCorrectly.wasPerformed
                    ).toBeTruthy();
                    // expect(paramLog.overriden).toBeTruthy(); // is not true for mock overrides
                    expect(
                        paramLog.resolvedWithDefault.wasPerformed
                    ).toBeFalsy();
                }

                expect(resolutionResult.resolved).toEqual({
                    modelId: testModelId,
                    tactics: simpleTactics,
                    systemPrompt: "",
                    maxTokensToGenerate: Math.max(
                        0,
                        ...simpleTactics.map((tactic) => tactic.length)
                    ),
                    tokensLimit: Number.MAX_SAFE_INTEGER,
                    maxContextTheoremsNumber: Number.MAX_SAFE_INTEGER,
                    multiroundProfile: {
                        maxRoundsNumber: 1,
                        defaultProofFixChoices: 0,
                        proofFixPrompt: "",
                        maxPreviousProofVersionsNumber: 0,
                    },
                    defaultChoices: simpleTactics.length,
                });
            }
        );
    });

    test("Test `generateProof` throws on invalid `choices`", async () => {
        await withPredefinedProofsProvider(
            ErrorsHandlingMode.RETHROW_ERRORS,
            async (predefinedProofsProvider) => {
                const resolvedParams = resolveParametersOrThrow(
                    predefinedProofsProvider,
                    inputParams
                );

                // non-positive choices
                await expect(async () => {
                    await predefinedProofsProvider.generateProof(
                        proofGenerationContext,
                        resolvedParams,
                        -1
                    );
                }).toBeRejectedWith(ConfigurationError, "choices");

                // choices > tactics.length
                await expect(async () => {
                    await predefinedProofsProvider.generateProof(
                        proofGenerationContext,
                        resolvedParams,
                        resolvedParams.tactics.length + 1
                    );
                }).toBeRejectedWith(ConfigurationError, "choices");
            }
        );
    });

    test("Test chat-related features throw", async () => {
        await withPredefinedProofsProvider(
            ErrorsHandlingMode.RETHROW_ERRORS,
            async (predefinedProofsProvider) => {
                const resolvedParams = resolveParametersOrThrow(
                    predefinedProofsProvider,
                    inputParams
                );
                await expect(async () => {
                    await predefinedProofsProvider.generateFromChat(
                        {
                            chat: [],
                            contextTheorems: [],
                            estimatedTokens: {
                                messagesTokens: 0,
                                maxTokensToGenerate: 0,
                                maxTokensInTotal: 0,
                            },
                        },
                        resolvedParams,
                        choices
                    );
                }).toBeRejectedWith(
                    ConfigurationError,
                    "does not support generation from chat"
                );

                const [generatedProof] =
                    await predefinedProofsProvider.generateProof(
                        proofGenerationContext,
                        resolvedParams,
                        1
                    );
                expect(generatedProof.canBeFixed()).toBeFalsy();
                await expect(
                    async () =>
                        await generatedProof.fixProof(
                            "pretend to be diagnostic",
                            3
                        )
                ).toBeRejectedWith(ConfigurationError, "cannot be fixed");
            }
        );
    });

    test("Test time to become available is zero", async () => {
        await withPredefinedProofsProvider(
            ErrorsHandlingMode.SWALLOW_ERRORS,
            async (predefinedProofsProvider) => {
                const resolvedParams = resolveParametersOrThrow(
                    predefinedProofsProvider,
                    inputParams
                );
                const cursedParams: PredefinedProofsModelParams = {
                    ...resolvedParams,
                    tactics: ["auto.", () => throwError("a curse")] as any[],
                };
                await predefinedProofsProvider.generateProof(
                    proofGenerationContext,
                    cursedParams,
                    cursedParams.tactics.length
                );
                await delay(4000);
                await predefinedProofsProvider.generateProof(
                    proofGenerationContext,
                    cursedParams,
                    cursedParams.tactics.length
                );
                // despite 2 failures with >= 4 secs interval, should be available right now
                expect(
                    predefinedProofsProvider.estimateTimeToBecomeAvailable()
                ).toEqual(timeZero);
            }
        );
    }).timeout(6000);
});
