import { benchmarkCompletionGenerationTask } from "./benchmarkCompletionGeneration/benchmarkTask";
import { BenchmarkingItem } from "./structures/benchmarkingItem";

// TODO: get Experiment as input?
export async function benchmark(benchmarkingItems: BenchmarkingItem[]) {
    // TODO: mutex for all tasks with same model (by condition) => model groups
    // groups = by same service & same model
    const itemPromises = benchmarkingItems.map((benchmarkingItem) => {
        return benchmarkCompletionGenerationTask(benchmarkingItem);
    });
    // TODO: handle errors? or tasks handle them by themselves surely?
    await Promise.allSettled(itemPromises);
    // TODO: just gather a list of returned BenchmarkedItem-s, create ExperimentResult
    // TODO: save as JSON
}
