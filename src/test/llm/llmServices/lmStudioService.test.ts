import { expect } from "earl";

import { ConfigurationError } from "../../../llm/llmServiceErrors";
import { ErrorsHandlingMode } from "../../../llm/llmServices/commonStructures/errorsHandlingMode";
import { LMStudioService } from "../../../llm/llmServices/lmStudio/lmStudioService";
import { LMStudioModelParams } from "../../../llm/llmServices/modelParams";
import { defaultSystemMessageContent } from "../../../llm/llmServices/utils/paramsResolvers/basicModelParamsResolvers";
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
import {
    defaultUserMultiroundProfile,
    testResolveParametersFailsWithSingleCause,
    testResolveValidCompleteParameters,
} from "../llmSpecificTestUtils/testResolveParameters";

suite("[LLMService] Test `LMStudioService`", function () {
    const lmStudioPort = process.env.LMSTUDIO_PORT;
    const choices = 15;
    const inputFile = ["small_document.v"];

    const requiredInputParamsTemplate = {
        modelId: testModelId,
        temperature: 1,
        choices: choices,
        maxTokensToGenerate: 2000,
        tokensLimit: 4000,
    };

    testIf(
        lmStudioPort !== undefined,
        "`LMSTUDIO_PORT` is not specified",
        this.title,
        `Simple generation: 1 request, ${choices} choices`,
        async () => {
            const inputParams: LMStudioUserModelParams = {
                ...requiredInputParamsTemplate,
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
    )?.timeout(30000);

    test("Test `resolveParameters` reads & accepts valid params", async () => {
        const inputParams: LMStudioUserModelParams = {
            ...requiredInputParamsTemplate,
            port: 1234,
        };
        await withLLMService(new LMStudioService(), async (lmStudioService) => {
            testResolveValidCompleteParameters(lmStudioService, inputParams);
            testResolveValidCompleteParameters(
                lmStudioService,
                {
                    ...inputParams,
                    systemPrompt: defaultSystemMessageContent,
                    multiroundProfile: defaultUserMultiroundProfile,
                },
                true
            );
        });
    });

    test("Test `resolveParameters` validates LMStudio-extended params (`port`)", async () => {
        const inputParams: LMStudioUserModelParams = {
            ...requiredInputParamsTemplate,
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
            ...requiredInputParamsTemplate,
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
