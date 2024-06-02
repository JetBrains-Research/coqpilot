import { BenchmarkedItem } from "../structures/benchmarkedItem";

// TODO: serialize properly
export function benchmarkedItemToJson(
    benchmarkedItem: BenchmarkedItem
): string {
    return JSON.stringify(benchmarkedItem, null, 2);
}

export function benchmarkedItemsToJson(
    benchmarkedItems: BenchmarkedItem[]
): string {
    return JSON.stringify(
        benchmarkedItems.map((item) => benchmarkedItemToJson(item)),
        null,
        2
    );
}
