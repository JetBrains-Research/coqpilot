import { toFormattedJsonString } from "../../../utils/printers";
import { BenchmarkedItem } from "../structures/benchmarkingResults/benchmarkedItem";

import { BasicJsonSerialization } from "./basicJson/serialization";

export function benchmarkedItemToJson(
    benchmarkedItem: BenchmarkedItem
): string {
    const serialized =
        BasicJsonSerialization.serializeBenchmarkedItem(benchmarkedItem);
    return toFormattedJsonString(serialized);
}

export function benchmarkedItemsToJson(
    benchmarkedItems: BenchmarkedItem[]
): string {
    return `[\n${benchmarkedItems
        .map((item) => benchmarkedItemToJson(item))
        .join(",\n")}\n]`;
}
