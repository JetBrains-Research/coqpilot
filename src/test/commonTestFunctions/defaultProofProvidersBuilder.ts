import {
    GenerationBundlesStorage,
    ResolvedGenerationBundles,
} from "../../proofProviders/generationBundles";
import {
    ModelParams,
    PredefinedProofsModelParams,
} from "../../proofProviders/impl/modelParams";
import { PredefinedProofsModelParamsResolver } from "../../proofProviders/impl/predefinedProofs/predefinedProofsModelParamsResolver";
import { PredefinedProofsProvider } from "../../proofProviders/impl/predefinedProofs/predefinedProofsProvider";
import { ProofProvider } from "../../proofProviders/impl/proofProvider";
import { ProofProviderIdentifier } from "../../proofProviders/impl/proofProviderIdentifier";
import { resolveOrThrow } from "../../proofProviders/impl/utils/resolveOrThrow";
import { ProofProvidersStorage } from "../../proofProviders/proofProvidersStorage";
import { PredefinedProofsUserModelParams } from "../../proofProviders/userModelParams";

export function createDefaultProofProviders(
    proofProviderCtors: (new (...args: any[]) => ProofProvider)[] = [
        PredefinedProofsProvider,
    ]
): ProofProvidersStorage {
    const proofProviders = new ProofProvidersStorage();
    try {
        for (const ctor of proofProviderCtors) {
            proofProviders.registerProofProvider(() => new ctor({}));
        }
        return proofProviders;
    } catch (e) {
        proofProviders.dispose();
        throw e;
    }
}

export function createPredefinedProofsModel(
    modelId: string = "predefined-proofs",
    predefinedProofs: string[] = [
        "intros.",
        "reflexivity.",
        "auto.",
        "assumption. intros.",
        "left. reflexivity.",
    ]
): PredefinedProofsModelParams {
    const inputModelParams: PredefinedProofsUserModelParams = {
        modelId: modelId,
        tactics: predefinedProofs,
    };
    return resolveOrThrow(
        new PredefinedProofsModelParamsResolver(),
        inputModelParams
    );
}

export function createBundles(
    proofProviders: ProofProvidersStorage,
    ...modelsWithIdentifier: [ProofProviderIdentifier, ModelParams[]][]
): ResolvedGenerationBundles {
    const bundles = new GenerationBundlesStorage<ModelParams>();
    for (const [identifier, models] of modelsWithIdentifier) {
        for (const proofProvider of proofProviders.getProofProviders(
            identifier
        )) {
            bundles.addBundle({
                proofProvider: proofProvider,
                models: models,
            });
        }
    }
    return bundles;
}

export function createPredefinedProofsBundles(
    proofProviders: ProofProvidersStorage,
    predefinedProofs: string[] | undefined = undefined
) {
    const model = createPredefinedProofsModel(undefined, predefinedProofs);
    return createBundles(proofProviders, [
        ProofProviderIdentifier.PREDEFINED_PROOFS,
        [model],
    ]);
}
