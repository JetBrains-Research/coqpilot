import { expect } from "earl";

import { ConfigurationError } from "../../../llm/llmServiceErrors";
import { ErrorsHandlingMode } from "../../../llm/llmServices/llmService";
import { LMStudioService } from "../../../llm/llmServices/lmStudio/lmStudioService";
import { LMStudioModelParams } from "../../../llm/llmServices/modelParams";
import { LMStudioUserModelParams } from "../../../llm/userModelParams";

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
import { testResolveParametersFailsWithSingleCause } from "../llmSpecificTestUtils/testResolveParameters";

suite("[LLMService] Test `LMStudioService`", function () {
    const lmStudioPort = process.env.LMSTUDIO_PORT;
    const choices = 15;
    const inputFile = ["small_document.v"];

    const completeInputParamsTemplate = {
        modelId: testModelId,
        temperature: 1,
        maxTokensToGenerate: 2000,
        tokensLimit: 4000,
        choices: choices,
    };

    testIf(
        lmStudioPort !== undefined,
        "`LMSTUDIO_PORT` is not specified",
        this.title,
        `Simple generation: 1 request, ${choices} choices`,
        async () => {
            const inputParams: LMStudioUserModelParams = {
                ...completeInputParamsTemplate,
                port: parseInt(lmStudioPort!),
            };
            const lmStudioService = new LMStudioService();
            await testLLMServiceCompletesAdmitFromFile(
                lmStudioService,
                inputParams,
                inputFile,
                choices
            );
        }
    );

    test("Test `resolveParameters` validates LMStudio-extended params (`port`)", async () => {
        const inputParams: LMStudioUserModelParams = {
            ...completeInputParamsTemplate,
            port: 1234,
        };
        await withLLMService(new LMStudioService(), async (lmStudioService) => {
            // port !in [0, 65535]
            testResolveParametersFailsWithSingleCause(
                lmStudioService,
                {
                    ...inputParams,
                    port: 100000,
                },
                "port"
            );
        });
    });

    test("Test `generateProof` throws on invalid `choices`", async () => {
        const inputParams: LMStudioUserModelParams = {
            ...completeInputParamsTemplate,
            port: 1234,
        };
        await withLLMServiceAndParams(
            new LMStudioService(),
            inputParams,
            async (lmStudioService, resolvedParams: LMStudioModelParams) => {
                // non-positive choices
                expect(async () => {
                    await lmStudioService.generateProof(
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
