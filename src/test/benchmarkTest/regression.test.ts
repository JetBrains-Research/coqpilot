import { expect } from "earl";

import {
    BenchmarkingBundle,
    BenchmarkingBundleWithModelsParams,
    BenchmarkingBundleWithTargets,
} from "../../benchmark/framework/experiment/setupDSL/benchmarkingBundleBuilder";
import { TargetsBuilder } from "../../benchmark/framework/experiment/setupDSL/targetsBuilder";
import { SingleWorkspaceExperiment } from "../../benchmark/framework/experiment/singleWorkspaceExperiment";
import { SeverityLevel } from "../../benchmark/framework/logging/benchmarkingLogger";
import { DatasetCacheUsageMode } from "../../benchmark/framework/structures/inputParameters/datasetCaching";
import { BenchTestServiceProvider } from "../../benchmark/framework/structures/llmServiceProvider/testImplementors/benchTestLLMServiceProvider";
import { BenchTestInputBenchmarkingModelParams } from "../../benchmark/framework/structures/llmServiceProvider/testImplementors/benchTestModelParams";
import { colorize } from "../../utils/colorLogging";
import { time, timeToMillis } from "../../utils/time";
import { createRelativeTmpDir } from "../commonTestFunctions/pathsResolver";

suite("[Benchmarking Framework Tests] Regression tests", () => {
    function buildExperimentWithBundle(
        bundle: BenchmarkingBundleWithTargets<any>
    ): SingleWorkspaceExperiment {
        const experiment = new SingleWorkspaceExperiment();
        bundle.addTo(experiment);
        return experiment;
    }

    async function runSmokeTestExperiment(
        experiment: SingleWorkspaceExperiment
    ) {
        let hasSuccessfullyFinished = false;
        try {
            await experiment.run(createRelativeTmpDir(), {
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
    }

    async function runSmokeTestExperimentWithBundle(
        modelsBundle: BenchmarkingBundleWithModelsParams<any>
    ) {
        const testTarget = new TargetsBuilder()
            .withWorkspaceRoot(
                ".test-standalone-files",
                "no-special-environment"
            )
            .withAdmitTargetsFromFile("test.v", "test")
            .buildInputTargets();
        const completeBundle = modelsBundle.withTargets(testTarget);
        const experiment = buildExperimentWithBundle(completeBundle);
        await runSmokeTestExperiment(experiment);
    }

    test("Smoke test: fill standalone file with predefined `auto`", async () => {
        const autoModel = new BenchmarkingBundle()
            .withLLMService("predefined")
            .withBenchmarkingModelsParamsCommons({
                ranker: "random",
            })
            .withBenchmarkingModelsParams({
                modelId: "prove-with-auto",
                tactics: ["auto."],
            });
        await runSmokeTestExperimentWithBundle(autoModel);
    }).timeout(timeToMillis(time(5, "minute")));

    test("Smoke test: fill standalone file via default `BenchTest`", async () => {
        const benchTestModel = new BenchmarkingBundle()
            .withCustomLLMService<BenchTestInputBenchmarkingModelParams>(
                () => new BenchTestServiceProvider()
            )
            .withBenchmarkingModelsParamsCommons({
                ranker: "random",
            })
            .withBenchmarkingModelsParams(
                {
                    generationMillis: 1_000,
                    modelId: "delayed-model",
                    tactics: ["invalid proof", "auto."],
                },
                {
                    generationMillis: 0,
                    modelId: "immediate-model",
                    tactics: ["invalid proof", "auto."],
                }
            );
        await runSmokeTestExperimentWithBundle(benchTestModel);
    }).timeout(timeToMillis(time(5, "minute")));

    test("Context theorems must not contain the target one", async () => {
        // TODO
    });
});
