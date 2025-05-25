import { expect } from "earl";

import { checkPrerequisitesAndInstallDefault } from "../../../../proofProviders/impl/abstractExternalProofProvider/installation/wrappers";
import { ErrorsHandlingMode } from "../../../../proofProviders/impl/commonStructures/errorsHandlingMode";
import {
    RangoModelMode,
    RangoModelParams,
} from "../../../../proofProviders/impl/modelParams";
import { RangoInstaller } from "../../../../proofProviders/impl/rango/rangoInstaller";
import { RangoService } from "../../../../proofProviders/impl/rango/rangoService";
import { resolveParametersOrThrow } from "../../../../proofProviders/impl/utils/resolveOrThrow";
import { ExternalPipelineProofGenerationContext } from "../../../../proofProviders/proofGenerationContext";
import {
    ConfigurationError,
    GenerationFailedError,
} from "../../../../proofProviders/proofProviderErrors";
import { RangoUserModelParams } from "../../../../proofProviders/userModelParams";

import { illegalState } from "../../../../utils/errors/throwErrors";
import { getCoqPilotMetaDirPath } from "../../../../utils/fs/coqPilotMetaDir";
import { deleteDirectory } from "../../../../utils/fs/directoryUtils";
import { appendToFile } from "../../../../utils/fs/fileUtils";
import { createTmpDirectory } from "../../../../utils/fs/tmpFs";
import { JsonSpacing, toJsonString } from "../../../../utils/printers";
import { time, timeToMillis } from "../../../../utils/time";
import { testIf } from "../../../commonTestFunctions/conditionalTest";
import { withProofProvider } from "../../../commonTestFunctions/withProofProvider";
import { testModelId } from "../../proofProvidersSpecificTestUtils/constants";
import {
    testProofProviderCompletesAdmitFromFile,
    testProofProviderInSetupEnvironment,
} from "../../proofProvidersSpecificTestUtils/testProofProviderInEnvironment";
import {
    testResolveParametersFailsWithSingleCause,
    testResolveValidCompleteParameters,
} from "../../proofProvidersSpecificTestUtils/testResolveParameters";

suite("[ProofProvider] Test `RangoService`", function () {
    const localCheckpointPath =
        process.env.TESTING_RANGO_IN_LOCAL_MODE_CHECKPOINT;
    const mappedToRemotePort = process.env.TESTING_RANGO_IN_REMOTE_MODE_PORT;
    const modelInferenceTimeoutSeconds = 600;

    const openAIApiKey = process.env.OPENAI_API_KEY;
    const mockTimeoutSeconds = 5;
    const inputFile = ["small_document.v"];

    const requiredInputParamsTemplate = {
        modelId: testModelId,
    };
    const expectedChoices = 1;

    this.beforeAll(async () => {
        console.error("Rango installation is required, installing...");
        await checkPrerequisitesAndInstallDefault(
            new RangoInstaller(),
            { enableModelCheckpointInstallation: true },
            (message) => console.error(`Rango installer: ${message}`)
        );
    }).timeout(timeToMillis(time(20, "minute")));

    function testGeneration(
        customInputParams: Partial<RangoUserModelParams>,
        timeoutSeconds: number,
        enableTest: boolean,
        testWillBeSkippedCause: string,
        suiteName: string
    ) {
        testIf(
            enableTest,
            testWillBeSkippedCause,
            suiteName,
            `Simple generation in "${customInputParams.mode!}" mode: 1 request, ${timeoutSeconds} seconds timeout`,
            async () => {
                const inputParams: RangoUserModelParams = {
                    ...requiredInputParamsTemplate,
                    timeoutSeconds: timeoutSeconds,
                    ...customInputParams,
                } as RangoUserModelParams;
                const rangoService = new RangoService();
                await testProofProviderCompletesAdmitFromFile(
                    rangoService,
                    inputParams,
                    inputFile,
                    expectedChoices
                );
            }
        )?.timeout(100_000);
    }
    testGeneration(
        {
            mode: "mockOpenAI",
            mockOpenAIApiKey: openAIApiKey!,
        },
        mockTimeoutSeconds,
        openAIApiKey !== undefined,
        "`OPENAI_API_KEY` is not specified",
        this.title
    );
    testGeneration(
        {
            mode: "local",
            localCheckpointPath: localCheckpointPath!,
        },
        modelInferenceTimeoutSeconds,
        localCheckpointPath !== undefined,
        "`TESTING_RANGO_IN_LOCAL_MODE_CHECKPOINT` is not specified",
        this.title
    );
    testGeneration(
        {
            mode: "remote",
            mappedToRemotePort: parseInt(mappedToRemotePort!),
        },
        modelInferenceTimeoutSeconds,
        mappedToRemotePort !== undefined,
        "`TESTING_RANGO_IN_REMOTE_MODE_PORT` is not specified",
        this.title
    );

    test("Test `resolveParameters` reads & accepts valid params", async () => {
        await withProofProvider(new RangoService(), async (rangoService) => {
            testResolveValidCompleteParameters(rangoService, {
                ...requiredInputParamsTemplate,
                mode: "local",
            });
            testResolveValidCompleteParameters(rangoService, {
                ...requiredInputParamsTemplate,
                mode: "remote",
            });
            testResolveValidCompleteParameters(rangoService, {
                ...requiredInputParamsTemplate,
                mode: "mockOpenAI",
                mockOpenAIApiKey: "non-defined",
            });
        });
    });

    test("Test `resolveParameters` validates Rango-extended params (`timeoutSeconds`)", async () => {
        const inputParams: RangoUserModelParams = {
            ...requiredInputParamsTemplate,
            mode: "mockOpenAI",
            mockOpenAIApiKey: "non-defined",
        };
        await withProofProvider(new RangoService(), async (rangoService) => {
            // `timeoutSeconds` should be positive
            testResolveParametersFailsWithSingleCause(
                rangoService,
                {
                    ...inputParams,
                    timeoutSeconds: 0,
                },
                "timeoutSeconds"
            );
            // `timeoutSeconds` should be less than the maximum allowed value in the `mockOpenAI` mode
            testResolveParametersFailsWithSingleCause(
                rangoService,
                {
                    ...inputParams,
                    timeoutSeconds: 99999,
                },
                "timeoutSeconds"
            );

            // port !in [0, 65535]
            testResolveParametersFailsWithSingleCause(
                rangoService,
                {
                    ...inputParams,
                    mode: "remote",
                    mappedToRemotePort: 100000,
                },
                "port"
            );

            // `dataLocDirectoryPath` should be absolute
            testResolveParametersFailsWithSingleCause(
                rangoService,
                {
                    ...inputParams,
                    dataLocDirectoryPath: "./",
                },
                "dataLocDirectoryPath"
            );
            // `dataLocDirectoryPath` should exist
            testResolveParametersFailsWithSingleCause(
                rangoService,
                {
                    ...inputParams,
                    dataLocDirectoryPath:
                        "/non-existing-directory-for-coqpilot-test",
                },
                "dataLocDirectoryPath"
            );
        });
    });

    test("Test `generateProof` throws on invalid configurations", async () => {
        const inputParams: RangoUserModelParams = {
            ...requiredInputParamsTemplate,
            mode: "mockOpenAI",
            mockOpenAIApiKey: "non-defined",
        };
        await testProofProviderInSetupEnvironment(
            new RangoService(),
            inputParams,
            inputFile,
            async (
                rangoService,
                resolvedParams,
                _environment,
                _completionContext,
                proofGenerationContext
            ) => {
                // non-positive choices
                await expect(async () => {
                    await rangoService.generateProof(
                        proofGenerationContext,
                        resolvedParams,
                        -1
                    );
                }).toBeRejectedWith(ConfigurationError, "choices");
            }
        );
    });

    function testThrowsGracefullyOnFail(
        customInputParams: Partial<RangoUserModelParams>,
        enableTest: boolean,
        testWillBeSkippedCause: string,
        suiteName: string
    ) {
        testIf(
            enableTest,
            testWillBeSkippedCause,
            suiteName,
            `Test \`generateProof\` throws gracefully if Rango unexpectedly fails: "${customInputParams.mode!}" mode`,
            async () => {
                const inputParams: RangoUserModelParams = {
                    ...requiredInputParamsTemplate,
                    ...customInputParams,
                } as RangoUserModelParams;
                await testProofProviderInSetupEnvironment(
                    new RangoService(),
                    inputParams,
                    inputFile,
                    async (
                        rangoService,
                        resolvedParams,
                        _environment,
                        _completionContext,
                        proofGenerationContext
                    ) => {
                        /*
                         * `proofGenerationContext.externalPipelineContext` contains an invalid `sourceTheoremStartLine`:
                         * there is no such theorem; therefore Rango is expected to fail
                         * while trying to find the target (after parsing the project)
                         */
                        await expect(async () => {
                            try {
                                const externalContext =
                                    proofGenerationContext.externalPipelineContext ??
                                    illegalState(
                                        "`ProofGenerationContext.externalPipelineContext` is expected to be built ",
                                        "by `testProofProviderInSetupEnvironment`"
                                    );
                                await rangoService.generateProof(
                                    {
                                        ...proofGenerationContext,
                                        externalPipelineContext: {
                                            ...externalContext,
                                            sourceTheoremStatementRange: {
                                                ...externalContext.sourceTheoremProofRange,
                                                start: {
                                                    line: 1000,
                                                    character: 0,
                                                },
                                            },
                                        } as ExternalPipelineProofGenerationContext,
                                    },
                                    resolvedParams
                                );
                            } finally {
                                const projectRootPath =
                                    proofGenerationContext
                                        .externalPipelineContext
                                        ?.projectRootPath ??
                                    illegalState(
                                        "`proofGenerationContext` created by `testProofProviderInSetupEnvironment` ",
                                        "is expected to contain built `externalPipelineContext`"
                                    );
                                const failedExecutionLogsDir =
                                    getCoqPilotMetaDirPath(projectRootPath);
                                deleteDirectory(failedExecutionLogsDir);
                            }
                        }).toBeRejectedWith(
                            GenerationFailedError,
                            "Rango process failed: exit code 1. Logs are available at"
                        );
                    }
                );
            }
        )?.timeout(100_000);
    }
    testThrowsGracefullyOnFail(
        {
            mode: "mockOpenAI",
            mockOpenAIApiKey: "a-key",
        },
        true,
        "always executes",
        this.title
    );
    testThrowsGracefullyOnFail(
        {
            mode: "local",
            localCheckpointPath: localCheckpointPath!,
        },
        localCheckpointPath !== undefined,
        "`TESTING_RANGO_IN_LOCAL_MODE_CHECKPOINT` is not specified",
        this.title
    );
    testThrowsGracefullyOnFail(
        {
            mode: "remote",
            mappedToRemotePort: parseInt(mappedToRemotePort!),
        },
        mappedToRemotePort !== undefined,
        "`TESTING_RANGO_IN_REMOTE_MODE_PORT` is not specified",
        this.title
    );

    function testParametersResolutionOverrides(
        mode: RangoModelMode,
        expectedParamsToBeOverriden: Partial<RangoUserModelParams>
    ) {
        test(`Test \`resolveParameters\` overrides params correctly: "${mode}" mode`, async () => {
            const inputParams: RangoUserModelParams = {
                ...requiredInputParamsTemplate,
                mode: mode,
                timeoutSeconds: mockTimeoutSeconds,
                localCheckpointPath: "./model-checkpoint",
                mappedToRemotePort: 5065,
                mockOpenAIApiKey: "a-key",
                enableWholeProjectDataPoints: true,
                dataLocDirectoryPath: createTmpDirectory(),
            } as RangoUserModelParams;
            await withProofProvider(
                new RangoService(),
                async (rangoService) => {
                    const resolutionResult = rangoService.resolveParameters({
                        ...inputParams,
                        timeoutSeconds: mockTimeoutSeconds,
                        choices: 15,
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
                        if (!paramLog.inputReadCorrectly.wasPerformed) {
                            appendToFile(
                                `${toJsonString(paramLog, JsonSpacing.DEFAULT_FORMATTED)}`,
                                "/Users/Gleb.Solovev/tabs/coqpilot/debug.txt",
                                () => {}
                            );
                        }
                        expect(
                            paramLog.inputReadCorrectly.wasPerformed
                        ).toBeTruthy();
                        // expect(paramLog.overriden).toBeTruthy(); // is not true for mock overrides
                        expect(
                            paramLog.resolvedWithDefault.wasPerformed
                        ).toBeFalsy();
                    }

                    expect(resolutionResult.resolved).toEqual({
                        ...inputParams,
                        systemPrompt: "",
                        maxTokensToGenerate: Number.MAX_SAFE_INTEGER,
                        tokensLimit: Number.MAX_SAFE_INTEGER,
                        maxContextTheoremsNumber: Number.MAX_SAFE_INTEGER,
                        multiroundProfile: {
                            maxRoundsNumber: 1,
                            defaultProofFixChoices: 0,
                            proofFixPrompt: "",
                            maxPreviousProofVersionsNumber: 0,
                        },
                        defaultChoices: 1,
                        ...expectedParamsToBeOverriden,
                    } as RangoModelParams);
                }
            );
        });
    }
    testParametersResolutionOverrides("mockOpenAI", {
        localCheckpointPath: "",
        mappedToRemotePort: 0,
    });
    testParametersResolutionOverrides("local", {
        mappedToRemotePort: 0,
        mockOpenAIApiKey: "",
    });
    testParametersResolutionOverrides("remote", {
        localCheckpointPath: "",
        mockOpenAIApiKey: "",
    });

    test("Test chat-related features throw", async () => {
        const inputParams: RangoUserModelParams = {
            ...requiredInputParamsTemplate,
            mode: "mockOpenAI",
            mockOpenAIApiKey: "non-defined",
        };
        await withProofProvider(
            new RangoService({
                errorsHandlingMode: ErrorsHandlingMode.RETHROW_ERRORS,
            }),
            async (rangoService) => {
                const resolvedParams = resolveParametersOrThrow(
                    rangoService,
                    inputParams
                );
                await expect(async () => {
                    await rangoService.generateFromChat(
                        {
                            chat: [],
                            contextTheorems: [],
                            estimatedTokens: {
                                messagesTokens: 0,
                                maxTokensToGenerate: 0,
                                maxTokensInTotal: 0,
                            },
                        },
                        resolvedParams
                    );
                }).toBeRejectedWith(
                    ConfigurationError,
                    "does not support generation from chat"
                );
                // TODO: the same can be tested for `RangoGeneratedProof` too, but it's too costy
            }
        );
    });
});
