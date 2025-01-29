import { expect } from "earl";

import { ConfigurationError } from "../../../llm/llmServiceErrors";
import { DeepSeekService } from "../../../llm/llmServices/deepSeek/deepSeekService";
import { DeepSeekModelParams } from "../../../llm/llmServices/modelParams";
import { DeepSeekUserModelParams } from "../../../llm/userModelParams";

import { testIf } from "../../commonTestFunctions/conditionalTest";
import {
    withLLMService,
    withLLMServiceAndParams,
} from "../../commonTestFunctions/withLLMService";
import {
    deepSeekModelName,
    mockProofGenerationContext,
    testModelId,
} from "../llmSpecificTestUtils/constants";
import { testLLMServiceCompletesAdmitFromFile } from "../llmSpecificTestUtils/testAdmitCompletion";
import {
    paramsResolvedWithBasicDefaults,
    testResolveValidCompleteParameters,
} from "../llmSpecificTestUtils/testResolveParameters";

suite("[LLMService] Test `DeepSeekService`", function () {
    const apiKey = process.env.DEEPSEEK_API_KEY;
    const choices = 15;
    const inputFile = ["small_document.v"];

    const requiredInputParamsTemplate = {
        modelId: testModelId,
        modelName: deepSeekModelName,
        temperature: 1,
        choices: choices,
    };

    testIf(
        apiKey !== undefined,
        "`DEEPSEEK_API_KEY` is not specified",
        this.title,
        `Simple generation: 1 request, ${choices} choices`,
        async () => {
            const inputParams: DeepSeekUserModelParams = {
                ...requiredInputParamsTemplate,
                apiKey: apiKey!,
            };
            const deepSeekService = new DeepSeekService();
            await testLLMServiceCompletesAdmitFromFile(
                deepSeekService,
                inputParams,
                inputFile,
                choices
            );
        }
    )?.timeout(5000);

    test("Test `resolveParameters` reads & accepts valid params", async () => {
        const inputParams: DeepSeekUserModelParams = {
            ...requiredInputParamsTemplate,
            apiKey: "undefined",
        };
        await withLLMService(new DeepSeekService(), async (deepSeekService) => {
            testResolveValidCompleteParameters(deepSeekService, inputParams);
            testResolveValidCompleteParameters(
                deepSeekService,
                {
                    ...inputParams,
                    ...paramsResolvedWithBasicDefaults,
                    maxTokensToGenerate: 2000,
                    tokensLimit: 4000,
                },
                true
            );
        });
    });

    test("Test `generateProof` throws on invalid configurations, <no api key needed>", async () => {
        const inputParams: DeepSeekUserModelParams = {
            ...requiredInputParamsTemplate,
            apiKey: "undefined",
        };
        await withLLMServiceAndParams(
            new DeepSeekService(),
            inputParams,
            async (deepSeekService, resolvedParams: DeepSeekModelParams) => {
                // non-positive choices
                await expect(async () => {
                    await deepSeekService.generateProof(
                        mockProofGenerationContext,
                        resolvedParams,
                        -1
                    );
                }).toBeRejectedWith(ConfigurationError, "choices");

                // incorrect api key
                await expect(async () => {
                    await deepSeekService.generateProof(
                        mockProofGenerationContext,
                        resolvedParams,
                        1
                    );
                }).toBeRejectedWith(ConfigurationError, "api key");
            }
        );
    });

    testIf(
        apiKey !== undefined,
        "`DEEPSEEK_API_KEY` is not specified",
        this.title,
        "Test `generateProof` throws on invalid configurations, <api key required>",
        async () => {
            const inputParams: DeepSeekUserModelParams = {
                ...requiredInputParamsTemplate,
                apiKey: apiKey!,
            };
            await withLLMServiceAndParams(
                new DeepSeekService(),
                inputParams,
                async (deepSeekService, resolvedParams) => {
                    // unknown model name
                    await expect(async () => {
                        await deepSeekService.generateProof(
                            mockProofGenerationContext,
                            {
                                ...resolvedParams,
                                modelName: "unknown",
                            } as DeepSeekModelParams,
                            1
                        );
                    }).toBeRejectedWith(ConfigurationError, "model name");

                    // context length exceeded (requested too many tokens for the completion)
                    await expect(async () => {
                        await deepSeekService.generateProof(
                            mockProofGenerationContext,
                            {
                                ...resolvedParams,
                                maxTokensToGenerate: 500_000,
                                tokensLimit: 1_000_000,
                            } as DeepSeekModelParams,
                            1
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
