import { benchmark } from "../benchmark";
import { SeverityLevel } from "../logging/benchmarkingLogger";
import { BenchmarkingItem } from "../structures/benchmarkingItem";
import { TargetType } from "../structures/completionGenerationTask";
import { ExperimentResults } from "../structures/experimentResults";
import { LLMServiceIdentifier } from "../structures/llmServiceIdentifier";
import { getRootDir, joinPaths, resolveAsAbsolutePath } from "../utils/fsUtils";

import { InputBenchmarkingModelParams } from "./inputBenchmarkingModelParams";
import { InputTargets, mergeInputTargets } from "./targetsBuilder";

export class Experiment {
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
        loggerSeverity: SeverityLevel
    ): Promise<ExperimentResults> {
        // TODO: build nix projects in dataset dir
        return benchmark(
            this.buildBenchmarkingItems(),
            resolveAsAbsolutePath(joinPaths(getRootDir(), artifactsDirPath)),
            loggerSeverity
        );
    }

    // TODO: add logging
    private buildBenchmarkingItems(): BenchmarkingItem[] {
        const experimentInputTargets = mergeInputTargets(
            this.bundles.map((bundle) => bundle.targets)
        );
        const benchmarkingItems: BenchmarkingItem[] = [];
        for (const bundle of this.bundles) {
            for (const [
                workspaceRoot,
                filePathToFileTargets,
            ] of bundle.targets.entries()) {
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
                        targetTypesForAllTheorems.push(
                            TargetType.PROVE_THEOREM
                        );
                    }
                    targetTypesForAllTheorems.forEach(
                        (targetType) => benchmarkingItems.push({}) // TODO: fill with data
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
                            (targetType) => benchmarkingItems.push({}) // TODO: fill with data
                        );
                    }
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
