import { expect } from "earl";

import { LLMService } from "../../../llm/llmServices/llmService";
import { ModelParams } from "../../../llm/llmServices/modelParams";
import { UserModelParams } from "../../../llm/userModelParams";

import { checkTheoremProven } from "../../commonTestFunctions/checkProofs";
import { withPreparedEnvironmentAndItsFirstContext } from "../../commonTestFunctions/prepareEnvironment";
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
            withPreparedEnvironmentAndItsFirstContext(
                resourcePath,
                undefined,
                async (
                    environment,
                    completionContext,
                    proofGenerationContext
                ) => {
                    const generatedProofs = await service.generateProof(
                        proofGenerationContext,
                        resolvedParams,
                        choices
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
    );
}
