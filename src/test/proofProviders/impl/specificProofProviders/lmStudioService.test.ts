import { expect } from "earl";

import { LMStudioService } from "../../../../proofProviders/impl/lmStudio/lmStudioService";
import { LMStudioModelParams } from "../../../../proofProviders/impl/modelParams";
import { ConfigurationError } from "../../../../proofProviders/proofProviderErrors";
import { LMStudioUserModelParams } from "../../../../proofProviders/userModelParams";

import { testIf } from "../../../commonTestFunctions/conditionalTest";
import {
    withProofProvider,
    withProofProviderAndParams,
} from "../../../commonTestFunctions/withProofProvider";
import {
    mockProofGenerationContext,
    testModelId,
} from "../../proofProvidersSpecificTestUtils/constants";
import { testProofProviderCompletesAdmitFromFile } from "../../proofProvidersSpecificTestUtils/testProofProviderInEnvironment";
import {
    paramsResolvedWithBasicDefaults,
    testResolveParametersFailsWithSingleCause,
    testResolveValidCompleteParameters,
} from "../../proofProvidersSpecificTestUtils/testResolveParameters";

suite("[ProofProvider] Test `LMStudioService`", function () {
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
            await testProofProviderCompletesAdmitFromFile(
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
        await withProofProvider(
            new LMStudioService(),
            async (lmStudioService) => {
                testResolveValidCompleteParameters(
                    lmStudioService,
                    inputParams
                );
                testResolveValidCompleteParameters(
                    lmStudioService,
                    {
                        ...inputParams,
                        ...paramsResolvedWithBasicDefaults,
                    },
                    true
                );
            }
        );
    });

    test("Test `resolveParameters` validates LMStudio-extended params (`port`)", async () => {
        const inputParams: LMStudioUserModelParams = {
            ...requiredInputParamsTemplate,
            port: 1234,
        };
        await withProofProvider(
            new LMStudioService(),
            async (lmStudioService) => {
                // port !in [0, 65535]
                testResolveParametersFailsWithSingleCause(
                    lmStudioService,
                    {
                        ...inputParams,
                        port: 100000,
                    },
                    "port"
                );
            }
        );
    });

    test("Test `generateProof` throws on invalid `choices`", async () => {
        const inputParams: LMStudioUserModelParams = {
            ...requiredInputParamsTemplate,
            port: 1234,
        };
        await withProofProviderAndParams(
            new LMStudioService(),
            inputParams,
            async (lmStudioService, resolvedParams: LMStudioModelParams) => {
                // non-positive choices
                await expect(async () => {
                    await lmStudioService.generateProof(
                        mockProofGenerationContext,
                        resolvedParams,
                        -1
                    );
                }).toBeRejectedWith(ConfigurationError, "choices");
            }
        );
    });
});
