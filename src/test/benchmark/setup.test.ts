import { expect } from "earl";

import { BenchmarkingBundle } from "./framework/experiment/benchmarkingBundleBuilder";
import { Experiment } from "./framework/experiment/experiment";
import { TargetsBuilder } from "./framework/experiment/targetsBuilder";
import { SeverityLevel } from "./framework/logging/benchmarkingLogger";

suite("Full-fledged benchmark", () => {
    const experiment = new Experiment();

    new BenchmarkingBundle()
        .withLLMService("predefined")
        .withBenchmarkingModelsParams({
            modelId: "prove-with-auto",
            tactics: ["auto."],
            ranker: "random",
        })
        .withTargets(
            new TargetsBuilder()
                .withoutWorkspaceRoot()
                .withAdmitTargetsFromFile("auto_benchmark.v")
                .buildInputTargets(),
            new TargetsBuilder()
                .withWorkspaceRoot("imm", "nix")
                .withAdmitTargetsFromFile("src/basic/Events.v")
                .buildInputTargets()
        )
        .addTo(experiment);

    test("Run benchmarking with auto", async () => {
        const experimentResults = await experiment.run("benchmarksOutput", {
            loggerSeverity: SeverityLevel.DEBUG,
            logsFilePath: "benchmarkLogs/logs.txt",
            enableSchedulingDebugLogs: true,
            enableSubprocessLifetimeDebugLogs: true,
            maxActiveSubprocessesNumber: 1,
        });
        expect(experimentResults.getBenchmarkedItems()).not.toBeEmpty();
    });
});
