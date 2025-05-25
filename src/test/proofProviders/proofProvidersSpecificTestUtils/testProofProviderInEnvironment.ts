import { expect } from "earl";

import { ModelParams } from "../../../proofProviders/impl/modelParams";
import { ProofProvider } from "../../../proofProviders/impl/proofProvider";
import { ProofGenerationContext } from "../../../proofProviders/proofGenerationContext";
import { UserModelParams } from "../../../proofProviders/userModelParams";

import { CompletionContext } from "../../../core/completionGenerationContext";

import { checkTheoremProven } from "../../commonTestFunctions/checkProofs";
import {
    PreparedEnvironment,
    withPreparedEnvironmentAndItsFirstContext,
} from "../../commonTestFunctions/prepareEnvironment";
import { withProofProviderAndParams } from "../../commonTestFunctions/withProofProvider";

export async function testProofProviderInSetupEnvironment<
    InputModelParams extends UserModelParams,
    ResolvedModelParams extends ModelParams,
>(
    proofProvider: ProofProvider<InputModelParams, ResolvedModelParams>,
    inputParams: InputModelParams,
    resourcePath: string[],
    block: (
        proofProvider: ProofProvider<InputModelParams, ResolvedModelParams>,
        resolvedParams: ResolvedModelParams,
        environment: PreparedEnvironment,
        completionContext: CompletionContext,
        proofGenerationContext: ProofGenerationContext
    ) => Promise<any>
) {
    return withProofProviderAndParams(
        proofProvider,
        inputParams,
        async (proofProvider, resolvedParams: ResolvedModelParams) =>
            withPreparedEnvironmentAndItsFirstContext(
                resourcePath,
                undefined,
                async (
                    environment,
                    completionContext,
                    proofGenerationContext
                ) => {
                    await block(
                        proofProvider,
                        resolvedParams,
                        environment,
                        completionContext,
                        proofGenerationContext
                    );
                }
            )
    );
}

export async function testProofProviderCompletesAdmitFromFile<
    InputModelParams extends UserModelParams,
    ResolvedModelParams extends ModelParams,
>(
    proofProvider: ProofProvider<InputModelParams, ResolvedModelParams>,
    inputParams: InputModelParams,
    resourcePath: string[],
    choices: number
) {
    return testProofProviderInSetupEnvironment(
        proofProvider,
        inputParams,
        resourcePath,
        async (
            proofProvider,
            resolvedParams,
            environment,
            completionContext,
            proofGenerationContext
        ) => {
            const generatedProofs = await proofProvider.generateProof(
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
