import { BenchmarkingBundle } from "./framework/experiment/setupDSL/benchmarkingBundleBuilder";
import { CacheTargets } from "./framework/experiment/setupDSL/datasetCacheBuilder";
import { TargetsBuilder } from "./framework/experiment/setupDSL/targetsBuilder";
import { TeamCityExperiment } from "./framework/experiment/teamCity/teamCityExperiment";
import { SeverityLevel } from "./framework/logging/benchmarkingLogger";
import { colorize } from "./framework/logging/colorLogging";
import { DatasetCacheUsageMode } from "./framework/structures/inputParameters/datasetCaching";

const experiment = new TeamCityExperiment();

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
            .withAdmitTargetsFromFile("auto_benchmark.v", "test", "test_thr")
            .withAdmitTargetsFromFile("mixed_benchmark.v", "add_comm")
            .buildInputTargets()
        // new TargetsBuilder()
        //     .withWorkspaceRoot("imm", "nix")
        //     .withAdmitTargetsFromFile("src/basic/Events.v")
        //     .buildInputTargets()
    )
    .addTo(experiment);

const datasetCacheDirectoryPath = "benchmarkLogs/.cache/";

experiment.updateRunOptions({
    loggerSeverity: SeverityLevel.INFO,
    maxActiveSubprocessesNumber: 1,
});

experiment
    .buildDatasetCache(
        datasetCacheDirectoryPath,
        CacheTargets.standaloneFiles()
    )
    .then(() =>
        experiment.buildLightweightBenchmarkingItems(
            "dataset/teamCityExampleInput",
            {
                datasetCacheDirectoryPath: datasetCacheDirectoryPath,
                datasetCacheUsage:
                    DatasetCacheUsageMode.EXTEND_CACHE_WITH_MISSING_TARGETS,
            }
        )
    )
    .then(
        () =>
            console.log(
                colorize(
                    "\nExperiment pipeline has successfully finished!\n",
                    "green"
                )
            ),
        (reason) =>
            console.error(
                colorize(`\nExperiment pipeline has failed: ${reason}\n`, "red")
            )
    );
