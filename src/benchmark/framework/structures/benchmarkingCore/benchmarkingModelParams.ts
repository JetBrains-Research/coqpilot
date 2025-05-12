import { LLMService } from "../../../../llm/llmServices/llmService";
import { ModelParams } from "../../../../llm/llmServices/modelParams";
import { UserModelParams } from "../../../../llm/userModelParams";

import { ContextTheoremsRanker } from "../../../../core/contextTheoremRanker/contextTheoremsRanker";

export interface BenchmarkingModelParams<
    ResolvedModelParams extends ModelParams,
> {
    theoremRanker: ContextTheoremsRanker;
    modelParams: ResolvedModelParams;
    llmService: LLMService<UserModelParams, ModelParams>;
}
