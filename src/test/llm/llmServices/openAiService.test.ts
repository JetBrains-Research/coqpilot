import { expect } from "earl";

import { ConfigurationError } from "../../../llm/llmServiceErrors";
import { ErrorsHandlingMode } from "../../../llm/llmServices/llmService";
import { OpenAiModelParams } from "../../../llm/llmServices/modelParams";
import { OpenAiService } from "../../../llm/llmServices/openai/openAiService";
import { defaultSystemMessageContent } from "../../../llm/llmServices/utils/paramsResolvers/basicModelParamsResolvers";
import { OpenAiUserModelParams } from "../../../llm/userModelParams";

import { testIf } from "../../commonTestFunctions/conditionalTest";
import {
    withLLMService,
    withLLMServiceAndParams,
} from "../../commonTestFunctions/withLLMService";
import {
    gptTurboModelName,
    mockProofGenerationContext,
    testModelId,
} from "../llmSpecificTestUtils/constants";
import { testLLMServiceCompletesAdmitFromFile } from "../llmSpecificTestUtils/testAdmitCompletion";
import {
    defaultUserMultiroundProfile,
    testResolveParametersFailsWithSingleCause,
    testResolveValidCompleteParameters,
} from "../llmSpecificTestUtils/testResolveParameters";

suite("[LLMService] Test `OpenAiService`", function () {
    const apiKey = process.env.OPENAI_API_KEY;
    const choices = 15;
    const inputFile = ["small_document.v"];

    const requiredInputParamsTemplate = {
        modelId: testModelId,
        modelName: gptTurboModelName,
        temperature: 1,
        choices: choices,
    };

    testIf(
        apiKey !== undefined,
        "`OPENAI_API_KEY` is not specified",
        this.title,
        `Simple generation: 1 request, ${choices} choices`,
        async () => {
            const inputParams: OpenAiUserModelParams = {
                ...requiredInputParamsTemplate,
                apiKey: apiKey!,
            };
            const openAiService = new OpenAiService();
            await testLLMServiceCompletesAdmitFromFile(
                openAiService,
                inputParams,
                inputFile,
                choices
            );
        }
    )?.timeout(5000);

    test("Test `resolveParameters` reads & accepts valid params", async () => {
        const inputParams: OpenAiUserModelParams = {
            ...requiredInputParamsTemplate,
            apiKey: "undefined",
        };
        await withLLMService(new OpenAiService(), async (openAiService) => {
            testResolveValidCompleteParameters(openAiService, inputParams);
            testResolveValidCompleteParameters(
                openAiService,
                {
                    ...inputParams,
                    systemPrompt: defaultSystemMessageContent,
                    maxTokensToGenerate: 2000,
                    tokensLimit: 4000,
                    multiroundProfile: defaultUserMultiroundProfile,
                },
                true
            );
        });
    });

    function testResolvesTokensWithDefault(
        modelName: string,
        expectedTokensLimit: number,
        expectedMaxTokensToGenerate: number
    ) {
        test(`Test \`resolveParameters\` resolves tokens with defaults: "${modelName}"`, async () => {
            const inputParams: OpenAiUserModelParams = {
                ...requiredInputParamsTemplate,
                apiKey: "undefined",
                modelName: modelName,
            };
            await withLLMService(new OpenAiService(), async (openAiService) => {
                const resolutionResult =
                    openAiService.resolveParameters(inputParams);
                expect(resolutionResult.resolved).not.toBeNullish();
                expect(resolutionResult.resolved!.tokensLimit).toEqual(
                    expectedTokensLimit
                );
                expect(resolutionResult.resolved!.maxTokensToGenerate).toEqual(
                    expectedMaxTokensToGenerate
                );
                // check it was resolution with default indeed
                expect(
                    resolutionResult.resolutionLogs.find(
                        (paramLog) =>
                            paramLog.inputParamName === "maxTokensToGenerate"
                    )?.resolvedWithDefault.wasPerformed
                ).toBeTruthy();
                expect(
                    resolutionResult.resolutionLogs.find(
                        (paramLog) => paramLog.inputParamName === "tokensLimit"
                    )?.resolvedWithDefault.wasPerformed
                ).toBeTruthy();
            });
        });
    }

    (
        [
            ["gpt-3.5-turbo-0301", 4096, 2048],
            ["gpt-3.5-turbo-0125", 16_385, 4096],
            ["gpt-4-32k-0314", 32_768, 4096],
        ] as [string, number, number][]
    ).forEach(
        ([modelName, expectedTokensLimit, expectedMaxTokensToGenerate]) => {
            testResolvesTokensWithDefault(
                modelName,
                expectedTokensLimit,
                expectedMaxTokensToGenerate
            );
        }
    );

    test("Test `resolveParameters` validates OpenAI-extended params (`temperature`) & tokens params", async () => {
        const inputParams: OpenAiUserModelParams = {
            ...requiredInputParamsTemplate,
            apiKey: "undefined",
        };
        await withLLMService(new OpenAiService(), async (openAiService) => {
            // `temperature` !in [0, 2]
            testResolveParametersFailsWithSingleCause(
                openAiService,
                {
                    ...inputParams,
                    temperature: 5,
                },
                "temperature"
            );

            // `maxTokensToGenerate` > known `maxTokensToGenerate` for the "gpt-3.5-turbo-0301" model
            testResolveParametersFailsWithSingleCause(
                openAiService,
                {
                    ...inputParams,
                    modelName: "gpt-3.5-turbo-0301",
                    maxTokensToGenerate: 5000,
                },
                "maxTokensToGenerate"
            );

            // `tokensLimit` > known `tokensLimit` for the "gpt-3.5-turbo-0301" model
            testResolveParametersFailsWithSingleCause(
                openAiService,
                {
                    ...inputParams,
                    modelName: "gpt-3.5-turbo-0301",
                    tokensLimit: 5000,
                },
                "tokensLimit"
            );
        });
    });

    test("Test `generateProof` throws on invalid configurations, <no api key needed>", async () => {
        const inputParams: OpenAiUserModelParams = {
            ...requiredInputParamsTemplate,
            apiKey: "undefined",
        };
        await withLLMServiceAndParams(
            new OpenAiService(),
            inputParams,
            async (openAiService, resolvedParams: OpenAiModelParams) => {
                // non-positive choices
                expect(async () => {
                    await openAiService.generateProof(
                        mockProofGenerationContext,
                        resolvedParams,
                        -1,
                        ErrorsHandlingMode.RETHROW_ERRORS
                    );
                }).toBeRejectedWith(ConfigurationError, "choices");

                // incorrect api key
                expect(async () => {
                    await openAiService.generateProof(
                        mockProofGenerationContext,
                        resolvedParams,
                        1,
                        ErrorsHandlingMode.RETHROW_ERRORS
                    );
                }).toBeRejectedWith(ConfigurationError, "api key");
            }
        );
    });

    testIf(
        apiKey !== undefined,
        "`OPENAI_API_KEY` is not specified",
        this.title,
        "Test `generateProof` throws on invalid configurations, <api key required>",
        async () => {
            const inputParams: OpenAiUserModelParams = {
                ...requiredInputParamsTemplate,
                apiKey: apiKey!,
            };
            await withLLMServiceAndParams(
                new OpenAiService(),
                inputParams,
                async (openAiService, resolvedParams) => {
                    // unknown model name
                    expect(async () => {
                        await openAiService.generateProof(
                            mockProofGenerationContext,
                            {
                                ...resolvedParams,
                                modelName: "unknown",
                            } as OpenAiModelParams,
                            1,
                            ErrorsHandlingMode.RETHROW_ERRORS
                        );
                    }).toBeRejectedWith(ConfigurationError, "model name");

                    // context length exceeded (requested too many tokens for the completion)
                    expect(async () => {
                        await openAiService.generateProof(
                            mockProofGenerationContext,
                            {
                                ...resolvedParams,
                                maxTokensToGenerate: 500_000,
                                tokensLimit: 1_000_000,
                            } as OpenAiModelParams,
                            1,
                            ErrorsHandlingMode.RETHROW_ERRORS
                        );
                    }).toBeRejectedWith(
                        ConfigurationError,
                        "`tokensLimit` and `maxTokensToGenerate`"
                    );
                }
            );
        }
    );
});
