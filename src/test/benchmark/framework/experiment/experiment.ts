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
import {
    MergedInputTargets,
    mergeRequestedTargets,
} from "./mergedInputTargets";
import { InputTargets } from "./targetsBuilder";

export type BaseInputBenchmarkingBundle =
    InputBenchmarkingBundle<InputBenchmarkingModelParams.Params>;

export interface InputBenchmarkingBundle<
    InputParams extends InputBenchmarkingModelParams.Params,
> extends NewInputBenchmarkingBundle<InputParams> {
    bundleId: number;
}

export interface NewInputBenchmarkingBundle<
    InputParams extends InputBenchmarkingModelParams.Params,
> {
    llmServiceIdentifier: LLMServiceIdentifier;
    inputBenchmarkingModelsParams: InputParams[];
    requestedTargets: InputTargets[];
}

export class Experiment {
    private mergedInputTargets: MergedInputTargets | undefined = undefined;

    constructor(private readonly bundles: BaseInputBenchmarkingBundle[] = []) {}

    addBundle(
        newBundle: NewInputBenchmarkingBundle<InputBenchmarkingModelParams.Params>
    ) {
        this.bundles.push({
            ...newBundle,
            bundleId: this.bundles.length,
        });
    }

    /**
     * @param artifactsDirPath empty directory path relative to the root directory.
     */
    async run(
        artifactsDirPath: string,
        inputRunOptions: Partial<ExperimentRunOptions>
    ): Promise<ExperimentResults> {
        this.mergedInputTargets = mergeRequestedTargets(this.bundles);
        const resolvedRunOptions =
            this.resolveExperimentRunOptions(inputRunOptions);

        const logger: BenchmarkingLogger = new BenchmarkingLoggerImpl(
            resolvedRunOptions.loggerSeverity,
            resolvedRunOptions.logsFilePath === undefined
                ? undefined
                : resolveAsAbsolutePath(
                      joinPaths(getRootDir(), resolvedRunOptions.logsFilePath)
                  )
        );
        const subprocessesScheduler = new SubprocessesScheduler(
            resolvedRunOptions.maxActiveSubprocessesNumber,
            resolvedRunOptions.enableSchedulingDebugLogs
        );

        const benchmarkingItems = await buildBenchmarkingItems(
            this.bundles,
            this.mergedInputTargets,
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
        if (this.mergedInputTargets === undefined) {
            throw Error(
                "`inputTargets` should be built before input options resolution"
            );
        }
        return {
            loggerSeverity: inputOptions.loggerSeverity ?? SeverityLevel.INFO,
            logsFilePath: inputOptions.logsFilePath,
            maxActiveSubprocessesNumber: Math.max(
                inputOptions.maxActiveSubprocessesNumber ??
                    this.mergedInputTargets.size,
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
