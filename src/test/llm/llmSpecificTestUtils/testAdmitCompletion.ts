import { expect } from "earl";

import { ErrorsHandlingMode } from "../../../llm/llmServices/commonStructures/errorsHandlingMode";
import { LLMService } from "../../../llm/llmServices/llmService";
import { ModelParams } from "../../../llm/llmServices/modelParams";
import { UserModelParams } from "../../../llm/userModelParams";

import { checkTheoremProven } from "../../commonTestFunctions/checkProofs";
import { prepareEnvironmentWithContexts } from "../../commonTestFunctions/prepareEnvironment";
import { withLLMServiceAndParams } from "../../commonTestFunctions/withLLMService";

export async function testLLMServiceCompletesAdmitFromFile<
    InputModelParams extends UserModelParams,
    ResolvedModelParams extends ModelParams,
>(
    service: LLMService<InputModelParams, ResolvedModelParams>,
    inputParams: InputModelParams,
    resourcePath: string[],
    choices: number
) {
    return withLLMServiceAndParams(
        service,
        inputParams,
        async (service, resolvedParams: ResolvedModelParams) => {
            const [environment, [[completionContext, proofGenerationContext]]] =
                await prepareEnvironmentWithContexts(resourcePath);
            const generatedProofs = await service.generateProof(
                proofGenerationContext,
                resolvedParams,
                choices,
                ErrorsHandlingMode.RETHROW_ERRORS
            );
            expect(generatedProofs).toHaveLength(choices);
            expect(
                checkTheoremProven(
                    generatedProofs,
                    completionContext,
                    environment
                )
            ).toBeTruthy();
        }
    );
}
