import { expect } from "earl";

import { LLMService } from "../../../llm/llmServices/llmService";
import { ModelParams } from "../../../llm/llmServices/modelParams";
import { ProofGenerationContext } from "../../../llm/proofGenerationContext";
import { UserModelParams } from "../../../llm/userModelParams";

import { CompletionContext } from "../../../core/completionGenerationContext";

import { checkTheoremProven } from "../../commonTestFunctions/checkProofs";
import {
    PreparedEnvironment,
    withPreparedEnvironmentAndItsFirstContext,
} from "../../commonTestFunctions/prepareEnvironment";
import { withLLMServiceAndParams } from "../../commonTestFunctions/withLLMService";

export async function testLLMServiceInSetupEnvironment<
    InputModelParams extends UserModelParams,
    ResolvedModelParams extends ModelParams,
>(
    service: LLMService<InputModelParams, ResolvedModelParams>,
    inputParams: InputModelParams,
    resourcePath: string[],
    block: (
        service: LLMService<InputModelParams, ResolvedModelParams>,
        resolvedParams: ResolvedModelParams,
        environment: PreparedEnvironment,
        completionContext: CompletionContext,
        proofGenerationContext: ProofGenerationContext
    ) => Promise<any>
) {
    return withLLMServiceAndParams(
        service,
        inputParams,
        async (service, resolvedParams: ResolvedModelParams) =>
            withPreparedEnvironmentAndItsFirstContext(
                resourcePath,
                undefined,
                async (
                    environment,
                    completionContext,
                    proofGenerationContext
                ) => {
                    await block(
                        service,
                        resolvedParams,
                        environment,
                        completionContext,
                        proofGenerationContext
                    );
                }
            )
    );
}

export async function testLLMServiceCompletesAdmitFromFile<
    InputModelParams extends UserModelParams,
    ResolvedModelParams extends ModelParams,
>(
    service: LLMService<InputModelParams, ResolvedModelParams>,
    inputParams: InputModelParams,
    resourcePath: string[],
    choices: number
) {
    return testLLMServiceInSetupEnvironment(
        service,
        inputParams,
        resourcePath,
        async (
            service,
            resolvedParams,
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
