import { BenchmarkedItem } from "./benchmarkedItem";

export class ExperimentResults {
    constructor(private readonly benchmarkedItems: BenchmarkedItem[]) {}

    getBenchmarkedItems(): BenchmarkedItem[] {
        return this.benchmarkedItems;
    }

    // TODO: add convenient getters

    // TODO: add JSON serialization-deserialization
}
