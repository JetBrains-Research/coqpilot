import { ModelParams } from "../../../../llm/llmServices/modelParams";

import { ContextTheoremsRanker } from "../../../../core/contextTheoremRanker/contextTheoremsRanker";

export interface BenchmarkingModelParams<
    ResolvedModelParams extends ModelParams,
> {
    theoremRanker?: ContextTheoremsRanker;
    modelParams: ResolvedModelParams;
}
