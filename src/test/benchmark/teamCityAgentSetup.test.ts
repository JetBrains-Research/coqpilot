import { TeamCityAgent } from "../../benchmark/framework/experiment/teamCity/teamCityAgent";
import { SeverityLevel } from "../../benchmark/framework/logging/benchmarkingLogger";
import { colorize } from "../../benchmark/framework/logging/colorLogging";
import { DatasetCacheUsageMode } from "../../benchmark/framework/structures/inputParameters/datasetCaching";
import { time, timeToMillis } from "../../utils/time";

suite("[SourceExecutable] Team City Benchmark Agent", () => {
    test("Run single workspace benchmark", async () => {
        const experiment = new TeamCityAgent(true, {
            loggerSeverity: SeverityLevel.DEBUG,
            datasetCacheDirectoryPath: "benchmarkLogs/.cache/",
            datasetCacheUsage: DatasetCacheUsageMode.READ_CACHE_ONLY,
        });

        try {
            await experiment.executeLightweightBenchmarkingItems(
                "dataset/teamCityExampleInput",
                "benchmarksOutput"
            );
            console.error(
                colorize(
                    "\nExperiment pipeline has successfully finished!\n",
                    "green"
                )
            );
        } catch (error) {
            console.error(
                colorize(`\nExperiment pipeline has failed: ${error}\n`, "red")
            );
        }
    }).timeout(timeToMillis(time(100, "minute")));
});
