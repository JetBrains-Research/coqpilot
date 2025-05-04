import { BenchmarkingBundle } from "../../benchmark/framework/experiment/setupDSL/benchmarkingBundleBuilder";
import { BenchTestServiceProvider } from "../../benchmark/framework/structures/llmServiceProvider/testImplementors/benchTestLLMServiceProvider";
import { BenchTestInputBenchmarkingModelParams } from "../../benchmark/framework/structures/llmServiceProvider/testImplementors/benchTestModelParams";

import {
    runSmokeTestExperimentWithBundle,
    testContextTheoremsNotContainTarget,
} from "./utils/specificTestsImpl";
import { BenchmarkingTestsConstants } from "./utils/testConstants";

import Constants = BenchmarkingTestsConstants;

suite("[Benchmarking Framework Tests] Regression tests", () => {
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
    }).timeout(Constants.SIMPLE_TEST_TIMEOUT);

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
    }).timeout(Constants.SIMPLE_TEST_TIMEOUT);

    test("Context theorems must not contain the target one", async () => {
        await testContextTheoremsNotContainTarget(
            "test_context_admit.v",
            "test",
            "admit"
        );
        await testContextTheoremsNotContainTarget(
            "test_context_proof.v",
            "test",
            "prove theorem"
        );
    }).timeout(Constants.SIMPLE_TEST_TIMEOUT);
});
