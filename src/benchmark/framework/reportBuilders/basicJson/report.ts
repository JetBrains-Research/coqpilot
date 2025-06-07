import { toFormattedJsonString } from "../../../../utils/printers";
import { BenchmarkedItem } from "../../structures/benchmarkingResults/benchmarkedItem";
import { AbstractReport } from "../utils/abstractReport";

import { BasicJsonSerialization } from "./serialization";

export function outputBasicJson(
    benchmarkedItems: BenchmarkedItem[],
    outputFilePath?: string
): string {
    return AbstractReport.outputContent(
        benchmarkedItemsToJson(benchmarkedItems),
        outputFilePath
    );
}

export function benchmarkedItemsToJson(
    benchmarkedItems: BenchmarkedItem[]
): string {
    return `[\n${benchmarkedItems
        .map((item) => benchmarkedItemToJson(item))
        .join(",\n")}\n]`;
}

export function benchmarkedItemToJson(
    benchmarkedItem: BenchmarkedItem
): string {
    const serialized =
        BasicJsonSerialization.serializeBenchmarkedItem(benchmarkedItem);
    return toFormattedJsonString(serialized);
}
