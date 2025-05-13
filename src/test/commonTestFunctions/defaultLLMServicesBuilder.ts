import {
    GenerationBundlesStorage,
    ResolvedGenerationBundles,
} from "../../llm/generationBundles";
import { LLMService } from "../../llm/llmServices/llmService";
import { LLMServiceIdentifier } from "../../llm/llmServices/llmServiceIdentifier";
import {
    ModelParams,
    PredefinedProofsModelParams,
} from "../../llm/llmServices/modelParams";
import { PredefinedProofsModelParamsResolver } from "../../llm/llmServices/predefinedProofs/predefinedProofsModelParamsResolver";
import { PredefinedProofsService } from "../../llm/llmServices/predefinedProofs/predefinedProofsService";
import { resolveOrThrow } from "../../llm/llmServices/utils/resolveOrThrow";
import { LLMServicesStorage } from "../../llm/llmServicesStorage";
import { PredefinedProofsUserModelParams } from "../../llm/userModelParams";

export function createDefaultServices(
    serviceCtors: (new (...args: any[]) => LLMService)[] = [
        PredefinedProofsService,
    ]
): LLMServicesStorage {
    const llmServices = new LLMServicesStorage();
    try {
        for (const ctor of serviceCtors) {
            llmServices.registerService(() => new ctor({}));
        }
        return llmServices;
    } catch (e) {
        llmServices.dispose();
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
    llmServices: LLMServicesStorage,
    ...modelsWithIdentifier: [LLMServiceIdentifier, ModelParams[]][]
): ResolvedGenerationBundles {
    const bundles = new GenerationBundlesStorage<ModelParams>();
    for (const [identifier, models] of modelsWithIdentifier) {
        for (const llmService of llmServices.getServices(identifier)) {
            bundles.addBundle({
                llmService: llmService,
                models: models,
            });
        }
    }
    return bundles;
}

export function createPredefinedProofsBundles(
    llmServices: LLMServicesStorage,
    predefinedProofs: string[] | undefined = undefined
) {
    const model = createPredefinedProofsModel(undefined, predefinedProofs);
    return createBundles(llmServices, [
        LLMServiceIdentifier.PREDEFINED_PROOFS,
        [model],
    ]);
}
