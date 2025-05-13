import { getOrPut } from "../utils/collectionUtils/mapUtils";
import { unsupported } from "../utils/errors/throwErrors";

import { LLMService } from "./llmServices/llmService";
import { LLMServiceIdentifier } from "./llmServices/llmServiceIdentifier";
import { ModelParams } from "./llmServices/modelParams";
import { UserModelParams } from "./userModelParams";

export interface GenerationBundle<
    Params extends UserModelParams | ModelParams,
    LLMServiceType extends LLMService<
        UserModelParams,
        ModelParams
    > = LLMService,
> {
    llmService: LLMServiceType;
    models: Params[];
}

export type ResolvedGenerationBundles = GenerationBundlesStorage<ModelParams>;

export class GenerationBundlesStorage<
    Params extends UserModelParams | ModelParams,
> {
    // TODO: support custom services by supporting undefined `LLMServiceIdentifier`
    private readonly identifierToBundles: Map<
        LLMServiceIdentifier,
        GenerationBundle<Params>[]
    > = new Map();

    getBundles(
        serviceTypeId: LLMServiceIdentifier
    ): GenerationBundle<Params>[] {
        return this.identifierToBundles.get(serviceTypeId) ?? [];
    }

    addBundle(bundle: GenerationBundle<Params>) {
        const key =
            bundle.llmService.identifier ??
            unsupported(
                "custom `LLMService` are not supported by `GenerationBundlesStorage`"
            );
        const sameServiceTypeBundles = getOrPut(
            this.identifierToBundles,
            key,
            () => [] as GenerationBundle<Params>[]
        );
        sameServiceTypeBundles.push(bundle);
    }

    allBundles(): GenerationBundle<Params>[] {
        return Array.from(this.identifierToBundles.values()).flat();
    }
}
