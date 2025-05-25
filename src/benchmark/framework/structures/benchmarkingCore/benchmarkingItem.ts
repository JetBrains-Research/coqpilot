import { ModelParams } from "../../../../proofProviders/impl/modelParams";

import { BenchmarkingModelParams } from "./benchmarkingModelParams";
import { CompletionGenerationTask } from "./completionGenerationTask";

export interface BenchmarkingItem {
    task: CompletionGenerationTask;
    params: BenchmarkingModelParams<ModelParams>;
}
