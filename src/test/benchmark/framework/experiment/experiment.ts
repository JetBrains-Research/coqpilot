import { benchmark } from "../benchmark";
import {
    BenchmarkingLogger,
    BenchmarkingLoggerImpl,
    SeverityLevel,
} from "../logging/benchmarkingLogger";
import { ExperimentResults } from "../structures/experimentResults";
import { ExperimentRunOptions } from "../structures/experimentRunOptions";
import { LLMServiceIdentifier } from "../structures/llmServiceIdentifier";
import { getRootDir, joinPaths, resolveAsAbsolutePath } from "../utils/fsUtils";
import { SubprocessesScheduler } from "../utils/subprocessUtils/subprocessesScheduler";

import { buildBenchmarkingItems } from "./buildBenchmarkingItems";
import { InputBenchmarkingModelParams } from "./inputBenchmarkingModelParams";
import { InputTargets, mergeInputTargets } from "./targetsBuilder";

export interface InputBenchmarkingBundle<
    InputParams extends InputBenchmarkingModelParams.Params,
> {
    llmServiceIdentifier: LLMServiceIdentifier;
    inputBenchmarkingModelsParams: InputParams[];
    targets: InputTargets;
}

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
        inputRunOptions: Partial<ExperimentRunOptions>
    ): Promise<ExperimentResults> {
        this.inputTargets = mergeInputTargets(
            this.bundles.map((bundle) => bundle.targets)
        );
        const resolvedRunOptions =
            this.resolveExperimentRunOptions(inputRunOptions);

        const logger: BenchmarkingLogger = new BenchmarkingLoggerImpl(
            resolvedRunOptions.loggerSeverity
        );
        const subprocessesScheduler = new SubprocessesScheduler(
            resolvedRunOptions.maxActiveSubprocessesNumber,
            resolvedRunOptions.enableSchedulingDebugLogs
        );
        const benchmarkingItems = await buildBenchmarkingItems(
            this.bundles,
            this.inputTargets,
            resolvedRunOptions,
            subprocessesScheduler,
            logger
        );

        return benchmark(
            benchmarkingItems,
            resolveAsAbsolutePath(joinPaths(getRootDir(), artifactsDirPath)),
            resolvedRunOptions,
            subprocessesScheduler,
            logger
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
            buildAndParseCoqProjectSubprocessTimeoutMillis:
                inputOptions.buildAndParseCoqProjectSubprocessTimeoutMillis,
            checkProofsSubprocessTimeoutMillis:
                inputOptions.checkProofsSubprocessTimeoutMillis,
            enableSubprocessLifetimeDebugLogs:
                inputOptions.enableSubprocessLifetimeDebugLogs ?? false,
            enableSchedulingDebugLogs:
                inputOptions.enableSchedulingDebugLogs ?? false,
        };
    }
}
