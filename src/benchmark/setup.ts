import { BenchmarkingBundle } from "./framework/experiment/benchmarkingBundleBuilder";
import { Experiment } from "./framework/experiment/experiment";
import { TargetsBuilder } from "./framework/experiment/targetsBuilder";
import { SeverityLevel } from "./framework/logging/benchmarkingLogger";
import { colorize } from "./framework/logging/colorLogging";

const experiment = new Experiment();

new BenchmarkingBundle()
    .withLLMService("openai")
    .withBenchmarkingModelsParamsCommons({
        ranker: "random",
        modelName: "gpt-3.5-turbo-0301",
        apiKey: "",
        choices: 1,
        maxTokensToGenerate: 1000,
        tokensLimit: 2000,
    })
    .withBenchmarkingModelsParams(
        {
            modelId: "openai-1",
            temperature: 0.5,
        },
        {
            modelId: "openai-2",
            temperature: 1.5,
        }
    )
    .withTargets(
        new TargetsBuilder()
            .withoutWorkspaceRoot()
            .withAdmitTargetsFromFile("auto_benchmark.v")
            .buildInputTargets()
        // new TargetsBuilder()
        //     .withWorkspaceRoot("imm", "nix")
        //     .withAdmitTargetsFromFile("src/basic/Events.v")
        //     .buildInputTargets()
    )
    .addTo(experiment);

const experimentResults = experiment.run("benchmarksOutput", {
    loggerSeverity: SeverityLevel.DEBUG,
    // logsFilePath: "benchmarkLogs/logs.txt",
    enableModelsSchedulingDebugLogs: true,
    maxActiveSubprocessesNumber: 1,
});

experimentResults.then(
    () =>
        console.log(
            colorize("\nExperiment has successfully finished!\n", "green")
        ),
    (reason) =>
        console.error(colorize(`\nExperiment has failed: ${reason}\n`, "red"))
);
