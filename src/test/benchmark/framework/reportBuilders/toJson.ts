import { BenchmarkedItem } from "../structures/benchmarkedItem";

// TODO: serialize properly
export function benchmarkedItemToJson(
    benchmarkedItem: BenchmarkedItem
): string {
    return JSON.stringify(benchmarkedItem, null, 2);
}
