import { benchmark } from "../benchmark";
import { SeverityLevel } from "../logging/benchmarkingLogger";
import { BenchmarkingItem } from "../structures/benchmarkingItem";
import { ExperimentResults } from "../structures/experimentResults";
import { LLMServiceIdentifier } from "../structures/llmServiceIdentifier";
import { getRootDir, joinPaths, resolveAsAbsolutePath } from "../utils/fsUtils";

import { InputBenchmarkingModelParams } from "./inputBenchmarkingModelParams";
import { InputTargets } from "./targetsBuilder";

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
        return benchmark(
            this.buildBenchmarkingItems(),
            resolveAsAbsolutePath(joinPaths(getRootDir(), artifactsDirPath)),
            loggerSeverity
        );
    }

    private buildBenchmarkingItems(): BenchmarkingItem[] {
        // TODO: implement
        return [];
    }
}

export interface InputBenchmarkingBundle<
    InputParams extends InputBenchmarkingModelParams.Params,
> {
    llmServiceIdentifier: LLMServiceIdentifier;
    inputBenchmarkingModelsParams: InputParams[];
    targets: InputTargets;
}
