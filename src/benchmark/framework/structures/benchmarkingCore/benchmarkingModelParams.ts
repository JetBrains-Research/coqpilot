import { ModelParams } from "../../../../llm/llmServices/modelParams";

import { ContextTheoremsRanker } from "../../../../core/contextTheoremRanker/contextTheoremsRanker";

import { LLMServiceIdentifier } from "../common/llmServiceIdentifier";

export interface BenchmarkingModelParams<
    ResolvedModelParams extends ModelParams,
> {
    theoremRanker: ContextTheoremsRanker;
    modelParams: ResolvedModelParams;
    llmServiceIdentifier: LLMServiceIdentifier;
}
