import { expect } from "earl";

import { ConfigurationError } from "../../../llm/llmServiceErrors";
import { GrazieService } from "../../../llm/llmServices/grazie/grazieService";
import { ErrorsHandlingMode } from "../../../llm/llmServices/llmService";
import { GrazieModelParams } from "../../../llm/llmServices/modelParams";
import { GrazieUserModelParams } from "../../../llm/userModelParams";

import { testIf } from "../../commonTestFunctions/conditionalTest";
import { resolveParametersOrThrow } from "../../commonTestFunctions/resolveOrThrow";
import {
    withLLMService,
    withLLMServiceAndParams,
} from "../../commonTestFunctions/withLLMService";
import {
    mockProofGenerationContext,
    testModelId,
} from "../llmSpecificTestUtils/constants";
import { testLLMServiceCompletesAdmitFromFile } from "../llmSpecificTestUtils/testAdmitCompletion";
import { testResolveValidCompleteParameters } from "../llmSpecificTestUtils/testResolveParameters";

suite("[LLMService] Test `GrazieService`", function () {
    const apiKey = process.env.GRAZIE_API_KEY;
    const choices = 15;
    const inputFile = ["small_document.v"];

    const completeInputParamsTemplate = {
        modelId: testModelId,
        modelName: "openai-gpt-4",
        choices: choices,
        maxTokensToGenerate: 2000,
        tokensLimit: 4000,
    };

    testIf(
        apiKey !== undefined,
        "`GRAZIE_API_KEY` is not specified",
        this.title,
        `Simple generation: 1 request, ${choices} choices`,
        async () => {
            const inputParams: GrazieUserModelParams = {
                ...completeInputParamsTemplate,
                apiKey: apiKey!,
            };
            const grazieService = new GrazieService();
            await testLLMServiceCompletesAdmitFromFile(
                grazieService,
                inputParams,
                inputFile,
                choices
            );
        }
    )?.timeout(6000);

    test("Test `resolveParameters` accepts valid params", async () => {
        const inputParams: GrazieUserModelParams = {
            ...completeInputParamsTemplate,
            apiKey: "undefined",
        };
        await withLLMService(new GrazieService(), async (grazieService) => {
            testResolveValidCompleteParameters(grazieService, inputParams);
        });
    });

    test("Resolve parameters with predefined `maxTokensToGenerate`", async () => {
        const inputParams: GrazieUserModelParams = {
            ...completeInputParamsTemplate,
            apiKey: "undefined",
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
            ...completeInputParamsTemplate,
            apiKey: "undefined",
        };
        await withLLMServiceAndParams(
            new GrazieService(),
            inputParams,
            async (grazieService, resolvedParams: GrazieModelParams) => {
                // non-positive choices
                expect(async () => {
                    await grazieService.generateProof(
                        mockProofGenerationContext,
                        resolvedParams,
                        -1,
                        ErrorsHandlingMode.RETHROW_ERRORS
                    );
                }).toBeRejectedWith(ConfigurationError, "choices");
            }
        );
    });
});
