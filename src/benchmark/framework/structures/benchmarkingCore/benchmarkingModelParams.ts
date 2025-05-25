import { ModelParams } from "../../../../proofProviders/impl/modelParams";
import { ProofProvider } from "../../../../proofProviders/impl/proofProvider";

import { ContextTheoremsRanker } from "../../../../core/contextTheoremRanker/contextTheoremsRanker";

export interface BenchmarkingModelParams<
    ResolvedModelParams extends ModelParams,
> {
    theoremRanker: ContextTheoremsRanker;
    modelParams: ResolvedModelParams;
    proofProvider: ProofProvider;
}
