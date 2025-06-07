import { ExperimentResults } from "../structures/benchmarkingResults/experimentResults";

import { outputBasicJson } from "./basicJson/report";
import { ModelsToAggregatedGroups } from "./modelsToAggregatedGroupsTable/report";

export namespace ReportBuilders {
    export function modelsToAggregatedGroupsTable(
        results: ExperimentResults,
        options: Partial<ModelsToAggregatedGroups.Options> = {}
    ): ModelsToAggregatedGroups.Report {
        return new ModelsToAggregatedGroups.Report(
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
