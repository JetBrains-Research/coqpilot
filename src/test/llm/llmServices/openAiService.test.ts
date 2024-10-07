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
    gptModelName,
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
        modelName: gptModelName,
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
        inputTokensLimit: number | undefined,
        expectedTokensLimit: number,
        expectedMaxTokensToGenerate: number,
        tokensLimitSuffix: string | undefined
    ) {
        const withDefinedTokensLimit =
            inputTokensLimit === undefined
                ? ""
                : ", defined input `tokensLimit`";
        test(`Test \`resolveParameters\` resolves tokens with defaults: "${modelName}"${withDefinedTokensLimit} ${tokensLimitSuffix}`, async () => {
            const inputParams: OpenAiUserModelParams = {
                ...requiredInputParamsTemplate,
                apiKey: "undefined",
                modelName: modelName,
                tokensLimit: inputTokensLimit,
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
                if (inputTokensLimit === undefined) {
                    expect(
                        resolutionResult.resolutionLogs.find(
                            (paramLog) =>
                                paramLog.inputParamName === "tokensLimit"
                        )?.resolvedWithDefault.wasPerformed
                    ).toBeTruthy();
                }
            });
        });
    }

    (
        [
            // just different models known to `OpenAiModelParamsResolver`
            [gptModelName, undefined, 128_000, 16_384, undefined],
            ["gpt-3.5-turbo-0125", undefined, 16_385, 4096, undefined],

            // input tokens limit value >= 2 * max tokens to generate, known max tokens is the answer
            [
                gptModelName,
                50_000,
                50_000,
                16_384,
                ">= 2 * `maxTokensToGenerate`",
            ],

            // input tokens limit value < 2 * max tokens to generate, 4096 is the answer
            [
                gptModelName,
                4096 * 2 + 1,
                4096 * 2 + 1,
                4096,
                "< 2 * `maxTokensToGenerate`",
            ],

            // input tokens limit value < 2 * max tokens to generate, known max tokens / 2 is the answer
            [
                "gpt-3.5-turbo-instruct",
                undefined,
                4096,
                2048,
                "< 2 * `maxTokensToGenerate`",
            ],
        ] as [string, number | undefined, number, number, string | undefined][]
    ).forEach(
        ([
            modelName,
            inputTokensLimit,
            expectedTokensLimit,
            expectedMaxTokensToGenerate,
            tokensLimitSuffix,
        ]) => {
            testResolvesTokensWithDefault(
                modelName,
                inputTokensLimit,
                expectedTokensLimit,
                expectedMaxTokensToGenerate,
                tokensLimitSuffix
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

            // `maxTokensToGenerate` > known `maxTokensToGenerate` for the "gpt-4o-mini-2024-07-18" model
            testResolveParametersFailsWithSingleCause(
                openAiService,
                {
                    ...inputParams,
                    modelName: gptModelName,
                    maxTokensToGenerate: 50_000,
                },
                "maxTokensToGenerate"
            );

            // `tokensLimit` > known `tokensLimit` for the "gpt-4o-mini-2024-07-18" model
            testResolveParametersFailsWithSingleCause(
                openAiService,
                {
                    ...inputParams,
                    modelName: gptModelName,
                    tokensLimit: 200_000,
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
