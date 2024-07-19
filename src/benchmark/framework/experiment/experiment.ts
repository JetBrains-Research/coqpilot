import { benchmark } from "../benchmark";
import { TimeMark } from "../benchmarkCompletionGeneration/measureUtils";
import {
    BenchmarkingLogger,
    BenchmarkingLoggerImpl,
    SeverityLevel,
} from "../logging/benchmarkingLogger";
import { ExperimentResults } from "../structures/experimentResults";
import { ExperimentRunOptions } from "../structures/experimentRunOptions";
import { LLMServiceIdentifier } from "../structures/llmServiceIdentifier";
import { AsyncScheduler } from "../utils/asyncScheduler";
import { getRootDir, joinPaths, resolveAsAbsolutePath } from "../utils/fsUtils";

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
        const totalTime = new TimeMark();

        const inputOptionsWithResolvedLoggerOptions =
            this.resolveLoggerOptions(inputRunOptions);
        const logger: BenchmarkingLogger = new BenchmarkingLoggerImpl(
            inputOptionsWithResolvedLoggerOptions.loggerSeverity,
            inputOptionsWithResolvedLoggerOptions.logsFilePath === undefined
                ? undefined
                : {
                      resolvedFilePath: resolveAsAbsolutePath(
                          joinPaths(
                              getRootDir(),
                              inputOptionsWithResolvedLoggerOptions.logsFilePath
                          )
                      ),
                      clearOnStart: true,
                  },
            "[Benchmarking]" // TODO: customize through run options
        );

        this.mergedInputTargets = mergeRequestedTargets(this.bundles, logger);
        const resolvedRunOptions = this.resolveAllExperimentRunOptions(
            inputOptionsWithResolvedLoggerOptions
        );

        const subprocessesScheduler = new AsyncScheduler(
            resolvedRunOptions.maxActiveSubprocessesNumber,
            resolvedRunOptions.enableSubprocessesSchedulingDebugLogs,
            "Subprocesses Scheduler"
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
            logger,
            totalTime
        );
    }

    private resolveLoggerOptions(
        inputOptions: Partial<ExperimentRunOptions>
    ): Partial<ExperimentRunOptions> & {
        loggerSeverity: SeverityLevel;
        logsFilePath: string | undefined;
    } {
        return {
            ...inputOptions,
            loggerSeverity: inputOptions.loggerSeverity ?? SeverityLevel.INFO,
            logsFilePath: inputOptions.logsFilePath,
        };
    }

    private resolveAllExperimentRunOptions(
        inputOptionsWithResolvedLoggerOptions: Partial<ExperimentRunOptions> & {
            loggerSeverity: SeverityLevel;
            logsFilePath: string | undefined;
        }
    ): ExperimentRunOptions {
        if (this.mergedInputTargets === undefined) {
            throw Error(
                "`inputTargets` should be built before input options resolution"
            );
        }
        return {
            loggerSeverity:
                inputOptionsWithResolvedLoggerOptions.loggerSeverity,
            logsFilePath: inputOptionsWithResolvedLoggerOptions.logsFilePath,

            maxActiveSubprocessesNumber: Math.max(
                inputOptionsWithResolvedLoggerOptions.maxActiveSubprocessesNumber ??
                    this.mergedInputTargets.size,
                1
            ),
            maxParallelGenerationRequestsToModel:
                inputOptionsWithResolvedLoggerOptions.maxParallelGenerationRequestsToModel ??
                1,

            buildAndParseCoqProjectSubprocessTimeoutMillis:
                inputOptionsWithResolvedLoggerOptions.buildAndParseCoqProjectSubprocessTimeoutMillis,
            checkProofsSubprocessTimeoutMillis:
                inputOptionsWithResolvedLoggerOptions.checkProofsSubprocessTimeoutMillis,

            enableSubprocessLifetimeDebugLogs:
                inputOptionsWithResolvedLoggerOptions.enableSubprocessLifetimeDebugLogs ??
                false,

            enableSubprocessesSchedulingDebugLogs:
                inputOptionsWithResolvedLoggerOptions.enableSubprocessesSchedulingDebugLogs ??
                false,
            enableModelsSchedulingDebugLogs:
                inputOptionsWithResolvedLoggerOptions.enableModelsSchedulingDebugLogs ??
                false,
        };
    }
}
