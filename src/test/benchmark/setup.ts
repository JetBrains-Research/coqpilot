import { expect } from "earl";

import { BenchmarkingBundle } from "./framework/experiment/benchmarkingBundle";
import { Experiment } from "./framework/experiment/experiment";
import { TargetsBuilder } from "./framework/experiment/targetsBuilder";
import { SeverityLevel } from "./framework/logging/benchmarkingLogger";

const experiment = new Experiment();

new BenchmarkingBundle()
    .withLLMService("grazie")
    .withBenchmarkingModelsParamsCommons({
        ranker: "random",
        tokensLimit: 2000,
        multiroundProfile: {
            maxRoundsNumber: 1,
        },
    })
    .withBenchmarkingModelsParams(
        {
            modelId: "grazie 1",
            modelName: "openai-gpt-4",
            apiKey: "apikey",
        },
        {
            modelId: "grazie 2",
            modelName: "openai-gpt-4",
            apiKey: "apikey",
            choices: 15,
            tokensLimit: 2000,
            ranker: "random",
        }
    )
    .withTargets(
        new TargetsBuilder()
            .withoutWorkspaceRoot()
            .withAdmitTargetsFromFile("file.v", "theorem1")
            .withAdmitTargetsFromFile("file.v", "theorem2", "theorem3")
            .buildInputTargets(),
        new TargetsBuilder()
            .withWorkspaceRoot("imm", "nix")
            .withProveTheoremTargetsFromDirectory("imm")
            .buildInputTargets()
    )
    .addTo(experiment);

test("Run benchmarking experiment", async () => {
    const experimentResults = await experiment.run(
        "benchmarksOutput",
        SeverityLevel.DEBUG
    );
    expect(experimentResults.getBenchmarkedItems()).not.toBeEmpty();
});
