import { benchmark } from "../benchmark";
import { TimeMark } from "../benchmarkCompletionGeneration/measureUtils";
import {
    BenchmarkingLogger,
    BenchmarkingLoggerImpl,
    SeverityLevel,
} from "../logging/benchmarkingLogger";
import { DatasetCacheUsageMode } from "../structures/datasetCaching";
import { ExperimentResults } from "../structures/experimentResults";
import { ExperimentRunOptions } from "../structures/experimentRunOptions";
import { InputBenchmarkingBundle } from "../structures/inputBenchmarkingBundle";
import {
    DatasetInputTargets,
    mergeInputTargets,
} from "../structures/inputTargets";
import { AsyncScheduler } from "../utils/asyncScheduler";
import { getRootDir, joinPaths, resolveAsAbsolutePath } from "../utils/fsUtils";

import { buildBenchmarkingItems } from "./buildBenchmarkingItems";

namespace CacheDirNames {
    export const defaultDatasetCacheDirectoryPath = "dataset/.parsingCache/";
}

export class Experiment {
    private mergedRequestedTargets: DatasetInputTargets | undefined = undefined;

    constructor(private readonly bundles: InputBenchmarkingBundle[] = []) {}

    addBundle(newBundle: InputBenchmarkingBundle) {
        this.bundles.push(newBundle);
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

        this.mergedRequestedTargets = mergeAndResolveRequestedTargets(
            this.bundles,
            logger
        );
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
            this.mergedRequestedTargets,
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
        if (this.mergedRequestedTargets === undefined) {
            throw Error(
                "`inputTargets` should be built before input options resolution"
            );
        }
        return {
            loggerSeverity:
                inputOptionsWithResolvedLoggerOptions.loggerSeverity,
            logsFilePath: inputOptionsWithResolvedLoggerOptions.logsFilePath,

            datasetCacheUsage:
                inputOptionsWithResolvedLoggerOptions.datasetCacheUsage ??
                DatasetCacheUsageMode.NO_CACHE_USAGE,
            datasetCacheDirectoryPath:
                inputOptionsWithResolvedLoggerOptions.datasetCacheDirectoryPath ??
                CacheDirNames.defaultDatasetCacheDirectoryPath,

            maxActiveSubprocessesNumber: Math.max(
                inputOptionsWithResolvedLoggerOptions.maxActiveSubprocessesNumber ??
                    this.mergedRequestedTargets.workspacesNumber(),
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

function mergeAndResolveRequestedTargets(
    inputBundles: InputBenchmarkingBundle[],
    logger: BenchmarkingLogger
): DatasetInputTargets {
    const mergedTargets = mergeInputTargets(
        inputBundles.map((bundle) => bundle.requestedTargets)
    ).resolveRequests();
    logger.debug(
        `Successfully merged requested targets: {\n${mergedTargets.toString()}\n}`
    );
    return mergedTargets;
}
