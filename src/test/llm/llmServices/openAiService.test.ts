import { expect } from "earl";

import { ConfigurationError } from "../../../llm/llmServiceErrors";
import { ErrorsHandlingMode } from "../../../llm/llmServices/llmService";
import { OpenAiModelParams } from "../../../llm/llmServices/modelParams";
import { OpenAiService } from "../../../llm/llmServices/openai/openAiService";
import { OpenAiUserModelParams } from "../../../llm/userModelParams";

import { testIf } from "../../commonTestFunctions/conditionalTest";
import { withLLMServiceAndParams } from "../../commonTestFunctions/withLLMService";
import {
    mockProofGenerationContext,
    testModelId,
} from "../llmSpecificTestUtils/constants";
import { testLLMServiceCompletesAdmitFromFile } from "../llmSpecificTestUtils/testAdmitCompletion";

suite("[LLMService] Test `OpenAiService`", function () {
    const apiKey = process.env.OPENAI_API_KEY;
    const choices = 15;
    const inputFile = ["small_document.v"];

    const completeUserParamsTemplate: OpenAiUserModelParams = {
        modelId: testModelId,
        modelName: "gpt-3.5-turbo-0301",
        temperature: 1,
        apiKey: "undefined",
        maxTokensToGenerate: 2000,
        tokensLimit: 4000,
    };

    testIf(
        apiKey !== undefined,
        "`OPENAI_API_KEY` is not specified",
        this.title,
        `Simple generation: 1 request, ${choices} choices`,
        async () => {
            const userParams: OpenAiUserModelParams = {
                ...completeUserParamsTemplate,
                apiKey: apiKey!,
            };
            const openAiService = new OpenAiService();
            await testLLMServiceCompletesAdmitFromFile(
                openAiService,
                userParams,
                inputFile,
                choices
            );
        }
    );

    test("Test throws on invalid configurations <no api key needed>", async () => {
        const userParams: OpenAiUserModelParams = {
            ...completeUserParamsTemplate,
            apiKey: "undefined",
        };
        await withLLMServiceAndParams(
            new OpenAiService(),
            userParams,
            async (openAiService, params) => {
                // non-positive choices
                expect(async () => {
                    await openAiService.generateProof(
                        mockProofGenerationContext,
                        params,
                        -1,
                        ErrorsHandlingMode.RETHROW_ERRORS
                    );
                }).toBeRejectedWith(ConfigurationError, "choices");

                // temperature !in [0, 2]
                expect(async () => {
                    await openAiService.generateProof(
                        mockProofGenerationContext,
                        { ...params, temperature: 5 } as OpenAiModelParams,
                        1,
                        ErrorsHandlingMode.RETHROW_ERRORS
                    );
                }).toBeRejectedWith(ConfigurationError, "temperature");

                // incorrect api key
                expect(async () => {
                    await openAiService.generateProof(
                        mockProofGenerationContext,
                        params,
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
        "Test throws on invalid configurations <api key required>",
        async () => {
            const userParams: OpenAiUserModelParams = {
                ...completeUserParamsTemplate,
                apiKey: apiKey!,
            };
            await withLLMServiceAndParams(
                new OpenAiService(),
                userParams,
                async (openAiService, params) => {
                    // unknown model name
                    expect(async () => {
                        await openAiService.generateProof(
                            mockProofGenerationContext,
                            {
                                ...params,
                                modelName: "unknown",
                            } as OpenAiModelParams,
                            1,
                            ErrorsHandlingMode.RETHROW_ERRORS
                        );
                    }).toBeRejectedWith(ConfigurationError, "model name");
                }
            );
        }
    );
});
