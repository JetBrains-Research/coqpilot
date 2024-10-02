import { BenchmarkingItem } from "../../structures/benchmarkingCore/benchmarkingItem";
import { getShortName } from "../../utils/commonStructuresUtils/llmServicesUtils";
import { getTargetTypeName } from "../../utils/serializationUtils";

export function logBenchmarkingItems(
    benchmarkingItems: BenchmarkingItem[]
): string {
    const benchmarkingItemsLogs = [];
    for (let i = 0; i < benchmarkingItems.length; i++) {
        benchmarkingItemsLogs.push(
            `Benchmarking item ${i}:\n${logBenchmarkingItem(benchmarkingItems[i])}`
        );
    }
    return benchmarkingItemsLogs.join("\n---\n");
}

function logBenchmarkingItem(benchmarkingItem: BenchmarkingItem): string {
    const task = benchmarkingItem.task;
    const targetLog = `* target: ${getTargetTypeName(task.targetType)}, goal \`${task.targetGoalToProveAsString}\``;
    const sourceLog = `* source: ${task.targetPositionRange} of theorem "${task.sourceTheorem.name}" from "${task.sourceFilePath}"`;
    const paramsLog = `* model id: "${benchmarkingItem.params.modelParams.modelId}"`; // TODO: support theorem ranker name
    const llmServiceLog = `* LLM service: ${getShortName(benchmarkingItem.params.llmServiceIdentifier)}`;
    return `${targetLog}\n${sourceLog}\n${paramsLog}\n${llmServiceLog}`;
}
