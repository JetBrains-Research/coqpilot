import { ModelParams } from "../../../llm/llmServices/modelParams";

import { BenchmarkingModelParams } from "./benchmarkingModelParams";
import { CompletionGenerationTask } from "./completionGenerationTask";

export interface BenchmarkingItem {
    task: CompletionGenerationTask;
    params: BenchmarkingModelParams<ModelParams>;
}
