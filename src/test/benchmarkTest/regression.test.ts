import { expect } from "earl";
import * as tmp from "tmp";

import { BenchmarkingBundle } from "../../benchmark/framework/experiment/setupDSL/benchmarkingBundleBuilder";
import { TargetsBuilder } from "../../benchmark/framework/experiment/setupDSL/targetsBuilder";
import { SingleWorkspaceExperiment } from "../../benchmark/framework/experiment/singleWorkspaceExperiment";
import { SeverityLevel } from "../../benchmark/framework/logging/benchmarkingLogger";
import { colorize } from "../../benchmark/framework/logging/colorLogging";
import { DatasetCacheUsageMode } from "../../benchmark/framework/structures/inputParameters/datasetCaching";
import { relativizeAbsolutePaths } from "../../benchmark/framework/utils/fileUtils/fs";
import { time, timeToMillis } from "../../utils/time";
import { getRootDir } from "../commonTestFunctions/pathsResolver";

suite("Benchmarking framework: regression tests", () => {
    // TODO: ideally, some special testing workspace
    // should be used instead of standalone files root

    test("Smoke test: fill standalone file with `auto`", async () => {
        const experiment = new SingleWorkspaceExperiment();

        new BenchmarkingBundle()
            .withLLMService("predefined")
            .withBenchmarkingModelsParamsCommons({
                ranker: "random",
            })
            .withBenchmarkingModelsParams({
                modelId: "prove-with-auto",
                tactics: ["auto."],
            })
            .withTargets(
                new TargetsBuilder()
                    .withStandaloneFilesRoot()
                    .withAdmitTargetsFromFile("auto_benchmark.v", "test")
                    .buildInputTargets()
            )
            .addTo(experiment);

        const tmpDirectoryPath = tmp.dirSync().name;
        const relativeTmpDir = relativizeAbsolutePaths(
            getRootDir(),
            tmpDirectoryPath
        );

        let hasSuccessfullyFinished = false;
        try {
            await experiment.run(relativeTmpDir, {
                loggerSeverity: SeverityLevel.ERROR,
                datasetCacheUsage: DatasetCacheUsageMode.NO_CACHE_USAGE,
            });
            hasSuccessfullyFinished = true;
        } catch (error) {
            console.error(
                colorize(`\nExperiment pipeline has failed: ${error}\n`, "red")
            );
        }
        expect(hasSuccessfullyFinished).toBeTruthy();
    }).timeout(timeToMillis(time(10, "minute")));

    test("Context theorems must not contain the target one", async () => {
        // TODO
    });
});
