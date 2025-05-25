import { getOrPut } from "../utils/collectionUtils/mapUtils";
import { unsupported } from "../utils/errors/throwErrors";

import { ModelParams } from "./impl/modelParams";
import { ProofProvider } from "./impl/proofProvider";
import { ProofProviderIdentifier } from "./impl/proofProviderIdentifier";
import { UserModelParams } from "./userModelParams";

export interface GenerationBundle<
    Params extends UserModelParams | ModelParams,
    ProofProviderType extends ProofProvider<
        UserModelParams,
        ModelParams
    > = ProofProvider,
> {
    proofProvider: ProofProviderType;
    models: Params[];
}

export type ResolvedGenerationBundles = GenerationBundlesStorage<ModelParams>;

export class GenerationBundlesStorage<
    Params extends UserModelParams | ModelParams,
> {
    // TODO: support custom proofProviders by supporting undefined `ProofProviderIdentifier`
    private readonly identifierToBundles: Map<
        ProofProviderIdentifier,
        GenerationBundle<Params>[]
    > = new Map();

    getBundles(
        proofProviderTypeId: ProofProviderIdentifier
    ): GenerationBundle<Params>[] {
        return this.identifierToBundles.get(proofProviderTypeId) ?? [];
    }

    addBundle(bundle: GenerationBundle<Params>) {
        const key =
            bundle.proofProvider.identifier ??
            unsupported(
                "custom `ProofProvider` are not supported by `GenerationBundlesStorage`"
            );
        const sameProofProviderTypeBundles = getOrPut(
            this.identifierToBundles,
            key,
            () => [] as GenerationBundle<Params>[]
        );
        sameProofProviderTypeBundles.push(bundle);
    }

    allBundles(): GenerationBundle<Params>[] {
        return Array.from(this.identifierToBundles.values()).flat();
    }
}
