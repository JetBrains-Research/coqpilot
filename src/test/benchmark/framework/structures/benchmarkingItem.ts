import { ModelParams } from "../../../../llm/llmServices/modelParams";

import { BenchmarkingModelParams } from "./benchmarkingModelParams";
import { CompletionGenerationTask } from "./completionGenerationTask";
import { LLMServiceIdentifier } from "./llmServiceIdentifier";

export interface BenchmarkingItem {
    task: CompletionGenerationTask;
    params: BenchmarkingModelParams<ModelParams>;
    llmServiceIdentifier: LLMServiceIdentifier;
}
