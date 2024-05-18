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
        maxTokensToGenerate: 2000,
        tokensLimit: 4000,
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
            // testResolveValidCompleteParameters(openAiService, inputParams);
            testResolveValidCompleteParameters(
                openAiService,
                {
                    ...inputParams,
                    systemPrompt: defaultSystemMessageContent,
                    multiroundProfile: defaultUserMultiroundProfile,
                },
                true
            );
        });
    });

    test("Test `resolveParameters` validates OpenAI-extended params (`temperature`)", async () => {
        const inputParams: OpenAiUserModelParams = {
            ...requiredInputParamsTemplate,
            apiKey: "undefined",
        };
        await withLLMService(new OpenAiService(), async (openAiService) => {
            // temperature !in [0, 2]
            testResolveParametersFailsWithSingleCause(
                openAiService,
                {
                    ...inputParams,
                    temperature: 5,
                },
                "temperature"
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
