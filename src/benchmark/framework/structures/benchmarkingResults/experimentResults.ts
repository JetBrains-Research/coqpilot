import { BenchmarkedItem } from "./benchmarkedItem";

/**
 * Results of the conducted experiment.
 *
 * They can be passed to one of the report builders
 * to output a nice serialization. Check `ReportsBuilders` for more details.
 *
 * So far only `getBenchmarkedItems()` getter is supported.
 * In the future, more methods to perform in-code analysis will be provided.
 */
export class ExperimentResults {
    constructor(private readonly benchmarkedItems: BenchmarkedItem[]) {}

    // TODO: add convenient getters

    getBenchmarkedItems(): BenchmarkedItem[] {
        return this.benchmarkedItems;
    }
}
