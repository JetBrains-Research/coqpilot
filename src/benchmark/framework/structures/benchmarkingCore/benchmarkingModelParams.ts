import { ModelParams } from "../../../../llm/llmServices/modelParams";

import { ContextTheoremsRanker } from "../../../../core/contextTheoremRanker/contextTheoremsRanker";

import { LLMServiceProvider } from "../llmServiceProvider/llmServiceProvider";

export interface BenchmarkingModelParams<
    ResolvedModelParams extends ModelParams,
> {
    theoremRanker: ContextTheoremsRanker;
    modelParams: ResolvedModelParams;
    llmServiceProvider: LLMServiceProvider;
}
