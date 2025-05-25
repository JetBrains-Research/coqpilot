import { ModelParams } from "../../proofProviders/impl/modelParams";
import { ProofProvider } from "../../proofProviders/impl/proofProvider";
import { resolveParametersOrThrow } from "../../proofProviders/impl/utils/resolveOrThrow";
import { UserModelParams } from "../../proofProviders/userModelParams";

export async function withProofProvider<
    InputModelParams extends UserModelParams,
    ResolvedModelParams extends ModelParams,
    ProofProviderType extends ProofProvider<
        InputModelParams,
        ResolvedModelParams
    >,
    T,
>(
    proofProvider: ProofProviderType,
    block: (proofProvider: ProofProviderType) => Promise<T>
): Promise<T> {
    try {
        return await block(proofProvider);
    } finally {
        proofProvider.dispose();
    }
}

export async function withProofProviderAndParams<
    InputModelParams extends UserModelParams,
    ResolvedModelParams extends ModelParams,
    ProofProviderType extends ProofProvider<
        InputModelParams,
        ResolvedModelParams
    >,
    T,
>(
    proofProvider: ProofProviderType,
    inputParams: InputModelParams,
    block: (
        proofProvider: ProofProviderType,
        resolvedParams: ResolvedModelParams
    ) => Promise<T>
): Promise<T> {
    try {
        const resolvedParams = resolveParametersOrThrow(
            proofProvider,
            inputParams
        );
        return await block(proofProvider, resolvedParams);
    } finally {
        proofProvider.dispose();
    }
}
