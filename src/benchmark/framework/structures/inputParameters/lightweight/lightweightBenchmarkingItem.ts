import { LightweightCompletionGenerationTask } from "./lightweightCompletionGenerationTask";

export interface LightweightBenchmarkingItem {
    task: LightweightCompletionGenerationTask;
    targetModelIds: string[];
}
