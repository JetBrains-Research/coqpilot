import { BenchmarkedItem } from "../structures/benchmarkingResults/benchmarkedItem";

// TODO: serialize properly
export function benchmarkedItemToJson(
    benchmarkedItem: BenchmarkedItem
): string {
    return JSON.stringify(benchmarkedItem, null, 2);
}

export function benchmarkedItemsToJson(
    benchmarkedItems: BenchmarkedItem[]
): string {
    return `[\n${benchmarkedItems
        .map((item) => benchmarkedItemToJson(item))
        .join(",\n")}\n]`;
}
