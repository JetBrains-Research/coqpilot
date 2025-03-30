import { expect } from "earl";

import {
    ConfigurationError,
    GenerationFailedError,
} from "../../../llm/llmServiceErrors";
import { ErrorsHandlingMode } from "../../../llm/llmServices/commonStructures/errorsHandlingMode";
import { RangoService } from "../../../llm/llmServices/rango/rangoService";
import { resolveParametersOrThrow } from "../../../llm/llmServices/utils/resolveOrThrow";
import { ExternalPipelineProofGenerationContext } from "../../../llm/proofGenerationContext";
import { MockRangoUserModelParams } from "../../../llm/userModelParams";

import { illegalState } from "../../../utils/errors/throwErrors";
import { getCoqPilotMetaDirPath } from "../../../utils/fs/coqPilotMetaDir";
import { deleteDirectory } from "../../../utils/fs/directoryUtils";
import { testIf } from "../../commonTestFunctions/conditionalTest";
import { withLLMService } from "../../commonTestFunctions/withLLMService";
import { testModelId } from "../llmSpecificTestUtils/constants";
import {
    testLLMServiceCompletesAdmitFromFile,
    testLLMServiceInSetupEnvironment,
} from "../llmSpecificTestUtils/testLLMServiceInEnvironment";
import {
    testResolveParametersFailsWithSingleCause,
    testResolveValidCompleteParameters,
} from "../llmSpecificTestUtils/testResolveParameters";

suite("[LLMService] Test `RangoService`", function () {
    const apiKey = process.env.OPENAI_API_KEY;
    const timeoutSeconds = 5;
    const inputFile = ["small_document.v"];

    const requiredInputParamsTemplate = {
        modelId: testModelId,
    };
    const expectedChoices = 1;

    testIf(
        apiKey !== undefined,
        "`OPENAI_API_KEY` is not specified",
        this.title,
        `Simple generation: 1 request, ${timeoutSeconds} seconds timeout`,
        async () => {
            const inputParams: MockRangoUserModelParams = {
                ...requiredInputParamsTemplate,
                openAiApiKey: apiKey!,
                timeoutSeconds: timeoutSeconds,
            };
            const rangoService = new RangoService();
            await testLLMServiceCompletesAdmitFromFile(
                rangoService,
                inputParams,
                inputFile,
                expectedChoices
            );
        }
    )?.timeout(15_000);

    test("Test `resolveParameters` reads & accepts valid params", async () => {
        const inputParams: MockRangoUserModelParams = {
            ...requiredInputParamsTemplate,
            openAiApiKey: "undefined",
        };
        await withLLMService(new RangoService(), async (rangoService) => {
            testResolveValidCompleteParameters(rangoService, inputParams);
        });
    });

    test("Test `resolveParameters` validates Rango-extended params (`timeoutSeconds`)", async () => {
        const inputParams: MockRangoUserModelParams = {
            ...requiredInputParamsTemplate,
            openAiApiKey: "undefined",
        };
        await withLLMService(new RangoService(), async (rangoService) => {
            // `timeoutSeconds` should be positive
            testResolveParametersFailsWithSingleCause(
                rangoService,
                {
                    ...inputParams,
                    timeoutSeconds: 0,
                },
                "timeoutSeconds"
            );
        });
    });

    test("Test `generateProof` throws on invalid configurations", async () => {
        const inputParams: MockRangoUserModelParams = {
            ...requiredInputParamsTemplate,
            openAiApiKey: "undefined",
        };
        await testLLMServiceInSetupEnvironment(
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

    test("Test `generateProof` throws gracefully if Rango unexpectedly fails", async () => {
        const inputParams: MockRangoUserModelParams = {
            ...requiredInputParamsTemplate,
            openAiApiKey: "undefined",
        };
        await testLLMServiceInSetupEnvironment(
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
                        await rangoService.generateProof(
                            {
                                ...proofGenerationContext,
                                externalPipelineContext: {
                                    ...proofGenerationContext.externalPipelineContext,
                                    sourceTheoremStartLine: 100,
                                } as ExternalPipelineProofGenerationContext,
                            },
                            resolvedParams
                        );
                    } finally {
                        const projectRootPath =
                            proofGenerationContext.externalPipelineContext
                                ?.projectRootPath ??
                            illegalState(
                                "`proofGenerationContext` created by `testLLMServiceInSetupEnvironment` ",
                                "is expected to contain built `externalPipelineContext`"
                            );
                        const failedExecutionLogsDir =
                            getCoqPilotMetaDirPath(projectRootPath);
                        deleteDirectory(failedExecutionLogsDir);
                    }
                }).toBeRejectedWith(
                    GenerationFailedError,
                    "Rango process failed (exit code 1): logs are available at"
                );
            }
        );
    }).timeout(10_000);

    test("Test `resolveParameters` overrides params correctly", async () => {
        const apiKey = "undefined";
        const inputParams: MockRangoUserModelParams = {
            ...requiredInputParamsTemplate,
            openAiApiKey: apiKey,
        };
        await withLLMService(new RangoService(), async (rangoService) => {
            const resolutionResult = rangoService.resolveParameters({
                ...inputParams,
                timeoutSeconds: timeoutSeconds,
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
                expect(paramLog.inputReadCorrectly.wasPerformed).toBeTruthy();
                // expect(paramLog.overriden).toBeTruthy(); // is not true for mock overrides
                expect(paramLog.resolvedWithDefault.wasPerformed).toBeFalsy();
            }

            expect(resolutionResult.resolved).toEqual({
                modelId: testModelId,
                openAiApiKey: apiKey,
                timeoutSeconds: timeoutSeconds,
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
            });
        });
    });

    test("Test chat-related features throw", async () => {
        const inputParams: MockRangoUserModelParams = {
            ...requiredInputParamsTemplate,
            openAiApiKey: "undefined",
        };
        await withLLMService(
            new RangoService(undefined, ErrorsHandlingMode.RETHROW_ERRORS),
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
