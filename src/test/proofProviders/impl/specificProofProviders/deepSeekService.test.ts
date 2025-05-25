import { expect } from "earl";

import { DeepSeekService } from "../../../../proofProviders/impl/deepSeek/deepSeekService";
import { DeepSeekModelParams } from "../../../../proofProviders/impl/modelParams";
import { ConfigurationError } from "../../../../proofProviders/proofProviderErrors";
import { DeepSeekUserModelParams } from "../../../../proofProviders/userModelParams";

import { testIf } from "../../../commonTestFunctions/conditionalTest";
import {
    withProofProvider,
    withProofProviderAndParams,
} from "../../../commonTestFunctions/withProofProvider";
import {
    deepSeekModelName,
    mockProofGenerationContext,
    testModelId,
} from "../../proofProvidersSpecificTestUtils/constants";
import { testProofProviderCompletesAdmitFromFile } from "../../proofProvidersSpecificTestUtils/testProofProviderInEnvironment";
import {
    paramsResolvedWithBasicDefaults,
    testResolveValidCompleteParameters,
} from "../../proofProvidersSpecificTestUtils/testResolveParameters";

suite("[ProofProvider] Test `DeepSeekService`", function () {
    const apiKey = process.env.DEEPSEEK_API_KEY;
    const choices = 15;
    const inputFile = ["small_document.v"];

    const requiredInputParamsTemplate = {
        modelId: testModelId,
        modelName: deepSeekModelName,
        temperature: 1,
        choices: choices,
        maxTokensToGenerate: 2000,
        tokensLimit: 4000,
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
            await testProofProviderCompletesAdmitFromFile(
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
        await withProofProvider(
            new DeepSeekService(),
            async (deepSeekService) => {
                testResolveValidCompleteParameters(
                    deepSeekService,
                    inputParams
                );
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
            }
        );
    });

    test("Test `generateProof` throws on invalid configurations, <no api key needed>", async () => {
        const inputParams: DeepSeekUserModelParams = {
            ...requiredInputParamsTemplate,
            apiKey: "undefined",
        };
        await withProofProviderAndParams(
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
            await withProofProviderAndParams(
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
