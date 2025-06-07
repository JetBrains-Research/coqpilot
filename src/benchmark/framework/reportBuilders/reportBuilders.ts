import { BenchmarkedItem } from "../structures/benchmarkingResults/benchmarkedItem";
import { ExperimentResults } from "../structures/benchmarkingResults/experimentResults";

import { outputBasicJson } from "./basicJson/report";
import { ModelsToAggregatedGroupsTable } from "./modelsToAggregatedGroupsTable/report";

export namespace ReportsBuilders {
    export function modelsToAggregatedGroupsTable(
        results: ExperimentResults,
        options: Partial<ModelsToAggregatedGroupsTable.Options>
    ): ModelsToAggregatedGroupsTable.Report {
        return new ModelsToAggregatedGroupsTable.Report(
            results.getBenchmarkedItems(),
            options
        );
    }

    export function toBasicJson(
        results: ExperimentResults,
        outputFilePath?: string
    ): string {
        return outputBasicJson(results.getBenchmarkedItems(), outputFilePath);
    }
}
