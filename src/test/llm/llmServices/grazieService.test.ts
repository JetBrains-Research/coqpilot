import { expect } from "earl";

import { ConfigurationError } from "../../../llm/llmServiceErrors";
import { GrazieService } from "../../../llm/llmServices/grazie/grazieService";
import { GrazieModelParams } from "../../../llm/llmServices/modelParams";
import { resolveParametersOrThrow } from "../../../llm/llmServices/utils/resolveOrThrow";
import { GrazieUserModelParams } from "../../../llm/userModelParams";

import { testIf } from "../../commonTestFunctions/conditionalTest";
import {
    withLLMService,
    withLLMServiceAndParams,
} from "../../commonTestFunctions/withLLMService";
import {
    mockProofGenerationContext,
    testModelId,
} from "../llmSpecificTestUtils/constants";
import { testLLMServiceCompletesAdmitFromFile } from "../llmSpecificTestUtils/testAdmitCompletion";
import {
    paramsResolvedWithBasicDefaults,
    testResolveValidCompleteParameters,
} from "../llmSpecificTestUtils/testResolveParameters";

suite("[LLMService] Test `GrazieService`", function () {
    const apiKey = process.env.GRAZIE_API_KEY;
    const authType = process.env.GRAZIE_AUTH_TYPE;
    const choices = 15;
    const inputFile = ["small_document.v"];

    const requiredInputParamsTemplate = {
        modelId: testModelId,
        modelName: "openai-gpt-4",
        choices: choices,
        maxTokensToGenerate: 2000,
        tokensLimit: 4000,
    };

    testIf(
        apiKey !== undefined && authType !== undefined,
        "`GRAZIE_API_KEY` or `GRAZIE_AUTH_TYPE` is not specified",
        this.title,
        `Simple generation: 1 request, ${choices} choices`,
        async () => {
            const inputParams: GrazieUserModelParams = {
                ...requiredInputParamsTemplate,
                apiKey: apiKey!,
                authType: authType!,
            };
            const grazieService = new GrazieService();
            await testLLMServiceCompletesAdmitFromFile(
                grazieService,
                inputParams,
                inputFile,
                choices
            );
        }
    )?.timeout(10000);

    test("Test `resolveParameters` reads & accepts valid params", async () => {
        const inputParams: GrazieUserModelParams = {
            ...requiredInputParamsTemplate,
            apiKey: "undefined",
            authType: "stgn",
        };
        await withLLMService(new GrazieService(), async (grazieService) => {
            testResolveValidCompleteParameters(grazieService, inputParams);
            testResolveValidCompleteParameters(
                grazieService,
                {
                    ...inputParams,
                    ...paramsResolvedWithBasicDefaults,
                },
                true
            );
        });
    });

    test("Resolve parameters with predefined `maxTokensToGenerate`", async () => {
        const inputParams: GrazieUserModelParams = {
            ...requiredInputParamsTemplate,
            apiKey: "undefined",
            authType: "stgn",
            maxTokensToGenerate: 6666, // should be overriden by GrazieService
        };
        withLLMService(new GrazieService(), async (grazieService) => {
            const resolvedParams = resolveParametersOrThrow(
                grazieService,
                inputParams
            );
            expect(resolvedParams.maxTokensToGenerate).toEqual(
                GrazieService.maxTokensToGeneratePredefined
            );
        });
    });

    test("Test `generateProof` throws on invalid `choices`", async () => {
        const inputParams: GrazieUserModelParams = {
            ...requiredInputParamsTemplate,
            apiKey: "undefined",
            authType: "stgn",
        };
        await withLLMServiceAndParams(
            new GrazieService(),
            inputParams,
            async (grazieService, resolvedParams: GrazieModelParams) => {
                // non-positive choices
                await expect(async () => {
                    await grazieService.generateProof(
                        mockProofGenerationContext,
                        resolvedParams,
                        -1
                    );
                }).toBeRejectedWith(ConfigurationError, "choices");
            }
        );
    });
});
