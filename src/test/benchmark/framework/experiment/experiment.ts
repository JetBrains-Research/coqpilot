import { benchmark } from "../benchmark";
import { SeverityLevel } from "../logging/benchmarkingLogger";
import { BenchmarkingItem } from "../structures/benchmarkingItem";
import { TargetType } from "../structures/completionGenerationTask";
import { ExperimentResults } from "../structures/experimentResults";
import { ExperimentRunOptions } from "../structures/experimentRunOptions";
import { LLMServiceIdentifier } from "../structures/llmServiceIdentifier";
import { getRootDir, joinPaths, resolveAsAbsolutePath } from "../utils/fsUtils";

import { InputBenchmarkingModelParams } from "./inputBenchmarkingModelParams";
import { InputTargets, mergeInputTargets } from "./targetsBuilder";

export class Experiment {
    private inputTargets: InputTargets | undefined = undefined;

    constructor(
        private readonly bundles: InputBenchmarkingBundle<InputBenchmarkingModelParams.Params>[] = []
    ) {}

    addBundle(
        bundle: InputBenchmarkingBundle<InputBenchmarkingModelParams.Params>
    ) {
        this.bundles.push(bundle);
    }

    /**
     * @param artifactsDirPath empty directory path relative to the root directory.
     */
    async run(
        artifactsDirPath: string,
        inputExperimentRunOptions: Partial<ExperimentRunOptions>
    ): Promise<ExperimentResults> {
        // TODO: build nix projects in dataset dir
        this.inputTargets = mergeInputTargets(
            this.bundles.map((bundle) => bundle.targets)
        );
        return benchmark(
            this.buildBenchmarkingItems(),
            resolveAsAbsolutePath(joinPaths(getRootDir(), artifactsDirPath)),
            this.resolveExperimentRunOptions(inputExperimentRunOptions)
        );
    }

    private resolveExperimentRunOptions(
        inputOptions: Partial<ExperimentRunOptions>
    ): ExperimentRunOptions {
        if (this.inputTargets === undefined) {
            throw Error(
                "`inputTargets` should be built before input options resolution"
            );
        }
        return {
            loggerSeverity: inputOptions.loggerSeverity ?? SeverityLevel.INFO,
            maxActiveSubprocessesNumber: Math.max(
                inputOptions.maxActiveSubprocessesNumber ??
                    this.inputTargets.size,
                1
            ),
            checkProofsSubprocessTimeoutMillis:
                inputOptions.checkProofsSubprocessTimeoutMillis,
            enableSubprocessLifetimeDebugLogs:
                inputOptions.enableSubprocessLifetimeDebugLogs ?? false,
            enableSchedulingDebugLogs:
                inputOptions.enableSchedulingDebugLogs ?? false,
        };
    }

    // TODO: add logging
    private buildBenchmarkingItems(): BenchmarkingItem[] {
        if (this.inputTargets === undefined) {
            throw Error(
                "`inputTargets` should be built before building benchmarking items"
            );
        }
        const benchmarkingItems: BenchmarkingItem[] = [];
        for (const [
            workspaceRoot,
            filePathToFileTargets,
        ] of this.inputTargets.entries()) {
            // TODO: enter workspace
            for (const [
                filePath,
                fileTarget,
            ] of filePathToFileTargets.entries()) {
                // TODO: parse source file
                const targetTypesForAllTheorems = [];
                if (fileTarget.allTheoremsAsAdmitTargets) {
                    targetTypesForAllTheorems.push(TargetType.ADMIT);
                }
                if (fileTarget.allTheoremsAsProveTheoremTargets) {
                    targetTypesForAllTheorems.push(TargetType.PROVE_THEOREM);
                }
                targetTypesForAllTheorems.forEach(
                    (targetType) =>
                        benchmarkingItems.push({} as BenchmarkingItem) // TODO: fill with data
                );
                for (const [
                    theoremName,
                    theoremTarget,
                ] of fileTarget.specificTheoremTargets) {
                    const targetTypes = [];
                    if (
                        theoremTarget.admitTargets &&
                        !fileTarget.allTheoremsAsAdmitTargets
                    ) {
                        targetTypes.push(TargetType.ADMIT);
                    }
                    if (
                        theoremTarget.proveTheoremTarget &&
                        !fileTarget.allTheoremsAsProveTheoremTargets
                    ) {
                        targetTypes.push(TargetType.PROVE_THEOREM);
                    }
                    targetTypes.forEach(
                        (targetType) =>
                            benchmarkingItems.push({} as BenchmarkingItem) // TODO: fill with data
                    );
                }
            }
        }
        return benchmarkingItems;
    }
}

export interface InputBenchmarkingBundle<
    InputParams extends InputBenchmarkingModelParams.Params,
> {
    llmServiceIdentifier: LLMServiceIdentifier;
    inputBenchmarkingModelsParams: InputParams[];
    targets: InputTargets;
}
