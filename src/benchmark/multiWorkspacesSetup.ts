import { colorize } from "../utils/colorLogging";

import { MultiWorkspacesExperiment } from "./framework/experiment/multiWorkspacesExperiment";
import { BenchmarkingBundle } from "./framework/experiment/setupDSL/benchmarkingBundleBuilder";
import { CacheTargets } from "./framework/experiment/setupDSL/datasetCacheBuilder";
import { TargetsBuilder } from "./framework/experiment/setupDSL/targetsBuilder";
import { SeverityLevel } from "./framework/logging/benchmarkingLogger";
import { DatasetCacheUsageMode } from "./framework/structures/inputParameters/datasetCaching";

const experiment = new MultiWorkspacesExperiment();

const standaloneTargets = new TargetsBuilder()
    .withStandaloneFilesRoot()
    .withAdmitTargetsFromFile("auto_benchmark.v", "test", "test_thr")
    .withAdmitTargetsFromFile("mixed_benchmark.v")
    .buildInputTargets();

// const immTargets = new TargetsBuilder()
//     .withWorkspaceRoot("imm", "nix")
//     .withProveTheoremTargetsFromFile("src/basic/Events.v")
//     .buildInputTargets();

new BenchmarkingBundle()
    .withLLMService("predefined")
    .withBenchmarkingModelsParamsCommons({
        ranker: "random",
    })
    .withBenchmarkingModelsParams(
        { modelId: "invalid-proof", tactics: ["a."] },
        { modelId: "prove-with-auto", tactics: ["auto."] }
    )
    .withTargets(standaloneTargets)
    .addTo(experiment);

experiment.updateRunOptions({
    loggerSeverity: SeverityLevel.DEBUG,
    // logsFilePath: "benchmarkLogs/logs.txt",
    maxActiveSubprocessesNumber: 1,
});

experiment
    .buildDatasetCache("benchmarkLogs/.cache/", CacheTargets.standaloneFiles())
    .then(() =>
        experiment.run("benchmarksOutput", {
            datasetCacheDirectoryPath: "benchmarkLogs/.cache/",
            datasetCacheUsage:
                DatasetCacheUsageMode.EXTEND_CACHE_WITH_MISSING_TARGETS,
        })
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
