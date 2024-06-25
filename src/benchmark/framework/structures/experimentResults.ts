import { benchmarkedItemsToJson } from "../reportBuilders/toJson";

import { BenchmarkedItem } from "./benchmarkedItem";

export class ExperimentResults {
    constructor(private readonly benchmarkedItems: BenchmarkedItem[]) {}

    getBenchmarkedItems(): BenchmarkedItem[] {
        return this.benchmarkedItems;
    }

    asJson(): string {
        return benchmarkedItemsToJson(this.benchmarkedItems);
    }

    // TODO: add convenient getters

    // TODO: add proper JSON serialization-deserialization
}
