import { BenchmarkingBundle } from "../../benchmark/framework/experiment/setupDSL/benchmarkingBundleBuilder";
import { CacheTargets } from "../../benchmark/framework/experiment/setupDSL/datasetCacheBuilder";
import { TargetsBuilder } from "../../benchmark/framework/experiment/setupDSL/targetsBuilder";
import { SingleWorkspaceExperiment } from "../../benchmark/framework/experiment/singleWorkspaceExperiment";
import { SeverityLevel } from "../../benchmark/framework/logging/benchmarkingLogger";
import { colorize } from "../../benchmark/framework/logging/colorLogging";
import { DatasetCacheUsageMode } from "../../benchmark/framework/structures/inputParameters/datasetCaching";
import { time, timeToMillis } from "../../utils/time";

suite("[SourceExecutable] Single Workspace Benchmark", () => {
    test("Run single workspace benchmark", async () => {
        const experiment = new SingleWorkspaceExperiment();

        new BenchmarkingBundle()
            .withLLMService("predefined")
            .withBenchmarkingModelsParamsCommons({
                ranker: "random",
            })
            .withBenchmarkingModelsParams(
                { modelId: "invalid-proof", tactics: ["a."] },
                { modelId: "prove-with-auto", tactics: ["auto."] }
            )
            .withTargets(
                new TargetsBuilder()
                    .withStandaloneFilesRoot()
                    .withAdmitTargetsFromFile(
                        "auto_benchmark.v",
                        "test",
                        "test_thr"
                    )
                    .buildInputTargets()
            )
            .addTo(experiment);

        experiment.updateRunOptions({
            loggerSeverity: SeverityLevel.DEBUG,
            // logsFilePath: "benchmarkLogs/logs.txt",

            // Don't forget to set up properly (or via `COQ_LSP_PATH`)
            coqLspServerPath: "coq-lsp",
        });

        try {
            await experiment.buildDatasetCache(
                "benchmarkLogs/.cache/",
                CacheTargets.standaloneFiles()
            );
            await experiment.run("benchmarksOutput", {
                datasetCacheDirectoryPath: "benchmarkLogs/.cache/",
                datasetCacheUsage: DatasetCacheUsageMode.READ_CACHE_ONLY,
            });
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
    }).timeout(timeToMillis(time(10, "minute")));
});
