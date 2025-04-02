import { BenchmarkingBundle } from "../../benchmark/framework/experiment/setupDSL/benchmarkingBundleBuilder";
import { CacheTargets } from "../../benchmark/framework/experiment/setupDSL/datasetCacheBuilder";
import { TargetsBuilder } from "../../benchmark/framework/experiment/setupDSL/targetsBuilder";
import { SingleWorkspaceExperiment } from "../../benchmark/framework/experiment/singleWorkspaceExperiment";
import { SeverityLevel } from "../../benchmark/framework/logging/benchmarkingLogger";
import { DatasetCacheUsageMode } from "../../benchmark/framework/structures/inputParameters/datasetCaching";
import { colorize } from "../../utils/colorLogging";
import { time, timeToMillis } from "../../utils/time";

suite("[SourceExecutable] Single Workspace Benchmark", () => {
    test("Run single workspace benchmark", async () => {
        const experiment = new SingleWorkspaceExperiment();

        new BenchmarkingBundle()
            .withLLMService("rango")
            .withBenchmarkingModelsParamsCommons({
                ranker: "random",
            })
            .withBenchmarkingModelsParams({
                modelId: "rango",
                openAiApiKey: "",
                timeoutSeconds: 10,
            })
            .withTargets(
                new TargetsBuilder()
                    .withStandaloneFilesRoot()
                    .withAdmitTargetsFromFile("mixed_benchmark.v", "test_thr")
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
                proofGenerationRetries: 1,
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
