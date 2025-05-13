import { BenchmarkingBundle } from "../../benchmark/framework/experiment/setupDSL/benchmarkingBundleBuilder";
import { testIf } from "../commonTestFunctions/conditionalTest";

import {
    runSmokeTestExperimentWithBundle,
    testProveTheoremWithRango,
} from "./utils/specificTestsImpl";
import { BenchmarkingTestsConstants } from "./utils/testConstants";

import Constants = BenchmarkingTestsConstants;

// suite("[Benchmarking Framework Tests] Benchmark Rango", function () {
suite("Benchmark Rango", function () {
    const openAIApiKey = process.env.OPENAI_API_KEY;

    const enableTests = openAIApiKey !== undefined;
    const testWillBeSkippedCause = "`OPENAI_API_KEY` is not specified";
    const suiteName = this.title;

    const rangoMockModel = new BenchmarkingBundle()
        .withLLMService("rango")
        .withBenchmarkingModelsParamsCommons({
            ranker: "random",
        })
        .withBenchmarkingModelsParams({
            modelId: "rango-mock-model",

            mode: "mockOpenAI",
            mockOpenAIApiKey: openAIApiKey,

            timeoutSeconds: 1, // our target is to test Rango starting proof generation, not its success
            enableWholeProjectDataPoints: false,
        });

    testIf(
        enableTests,
        testWillBeSkippedCause,
        suiteName,
        'Run in "mockOpenAI" mode: basic admitted theorem`',
        async () => runSmokeTestExperimentWithBundle(rangoMockModel)
    )?.timeout(Constants.SIMPLE_TEST_TIMEOUT);

    testIf(
        enableTests,
        testWillBeSkippedCause,
        suiteName,
        'Run in "mockOpenAI" mode: whole theorem`',
        async () =>
            testProveTheoremWithRango("test_whole_proof.v", rangoMockModel)
    )?.timeout(Constants.SIMPLE_TEST_TIMEOUT);

    testIf(
        enableTests,
        testWillBeSkippedCause,
        suiteName,
        'Run in "mockOpenAI" mode: whole theorem with global variables & indent`',
        async () =>
            testProveTheoremWithRango(
                "test_whole_proof_global_variables_with_indent.v",
                rangoMockModel
            )
    )?.timeout(Constants.SIMPLE_TEST_TIMEOUT);
});
