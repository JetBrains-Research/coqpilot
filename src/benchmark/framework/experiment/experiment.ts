import { benchmark } from "../benchmark";
import { TimeMark } from "../benchmarkCompletionGeneration/measureUtils";
import {
    BenchmarkingLogger,
    BenchmarkingLoggerImpl,
    SeverityLevel,
} from "../logging/benchmarkingLogger";
import { parseDatasetForBenchmarkingItems } from "../parseDataset/core/parseDatasetForBenchmarkingItems";
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

import {
    CacheTargetsImpl,
    DatasetCacheBuildingImpl,
} from "./datasetCacheBuilder";

namespace CacheDirNames {
    export const defaultDatasetCacheDirectoryPath = "dataset/.parsingCache/";
}

export class Experiment {
    constructor(
        private readonly bundles: InputBenchmarkingBundle[] = [],
        private sharedRunOptions: Partial<ExperimentRunOptions> = {}
    ) {}

    addBundle(newBundle: InputBenchmarkingBundle) {
        this.bundles.push(newBundle);
    }

    /**
     * Updates experiment run options with ones specified in `runOptions`.
     * Changes made are applied to **all** further runs.
     * The properties that are not specified stay unchanged.
     */
    updateRunOptions(runOptions: Partial<ExperimentRunOptions>) {
        this.sharedRunOptions = {
            ...this.sharedRunOptions,
            ...runOptions,
        };
    }

    /**
     * Builds dataset cache for the requested targets.
     * The returning promise resolves successfully if and only if the operation succeeded.
     *
     * *Warning:* `datasetCacheDirectoryPath` content will be cleared before saving the built cache.
     *
     * @param datasetCacheDirectoryPath a directory to save cache into. Overrides the same-name property of the experiment run options.
     * @param cacheTargetsBuilders cache-building targets can be specified via `CacheTargets` builders.
     */
    async buildDatasetCache(
        datasetCacheDirectoryPath: string,
        ...cacheTargetsBuilders: CacheTargetsImpl.CacheTargetsBuilder[]
    ) {
        const executionContext = this.prepareExecutionContext(
            {
                ...this.sharedRunOptions,
                datasetCacheDirectoryPath: datasetCacheDirectoryPath,
            },
            "[Dataset Cache Building]",
            (logger) =>
                CacheTargetsImpl.buildCacheTargets(cacheTargetsBuilders, logger)
        );
        await DatasetCacheBuildingImpl.buildDatasetCache(
            executionContext.requestedTargets,
            executionContext.resolvedRunOptions,
            executionContext.subprocessesScheduler,
            executionContext.logger
        );
    }

    /**
     * @param artifactsDirPath empty directory path relative to the root directory.
     * @param runOptions properties to update the options for **this** run with. To save the updated options for the further runs use `Experiment.updateRunOptions(...)` method instead.
     */
    async run(
        artifactsDirPath: string,
        runOptions: Partial<ExperimentRunOptions> = {}
    ): Promise<ExperimentResults> {
        const executionContext = this.prepareExecutionContext(
            {
                ...this.sharedRunOptions,
                ...runOptions,
            },
            "[Benchmarking]", // TODO: customize through run options
            (logger) => mergeAndResolveRequestedTargets(this.bundles, logger)
        );
        const totalTime = new TimeMark();

        const benchmarkingItems = await parseDatasetForBenchmarkingItems(
            this.bundles,
            executionContext.requestedTargets,
            executionContext.resolvedRunOptions,
            executionContext.subprocessesScheduler,
            executionContext.logger
        );
        if (benchmarkingItems.length === 0) {
            throw Error(
                "No items to benchmark: make sure the experiment input is configured correctly."
            );
        }

        return benchmark(
            benchmarkingItems,
            resolveAsAbsolutePath(joinPaths(getRootDir(), artifactsDirPath)),
            executionContext.resolvedRunOptions,
            executionContext.subprocessesScheduler,
            executionContext.logger,
            totalTime
        );
    }

    private prepareExecutionContext(
        runOptions: Partial<ExperimentRunOptions>,
        loggerIdentifier: string,
        buildRequestedTargets: (
            logger: BenchmarkingLogger
        ) => DatasetInputTargets
    ): ExecutionContext {
        const optionsAfterStartupResolution =
            this.resolveOnStartupOptions(runOptions);
        const logger = this.initLogger(
            optionsAfterStartupResolution,
            loggerIdentifier
        );

        const requestedTargets = buildRequestedTargets(logger);
        const resolvedRunOptions = this.resolveAllExperimentRunOptions(
            optionsAfterStartupResolution,
            requestedTargets
        );

        const subprocessesScheduler = new AsyncScheduler(
            resolvedRunOptions.maxActiveSubprocessesNumber,
            resolvedRunOptions.enableSubprocessesSchedulingDebugLogs,
            "Subprocesses Scheduler"
        );

        return {
            requestedTargets: requestedTargets,
            resolvedRunOptions: resolvedRunOptions,
            subprocessesScheduler: subprocessesScheduler,
            logger: logger,
        };
    }

    private initLogger(
        optionsAfterStartupResolution: ExperimentRunOptions.AfterStartupResolution,
        recordIdentifier: string
    ): BenchmarkingLogger {
        return new BenchmarkingLoggerImpl(
            optionsAfterStartupResolution.loggerSeverity,
            optionsAfterStartupResolution.logsFilePath === undefined
                ? undefined
                : {
                      resolvedFilePath: resolveAsAbsolutePath(
                          joinPaths(
                              getRootDir(),
                              optionsAfterStartupResolution.logsFilePath
                          )
                      ),
                      clearOnStart: true,
                  },
            recordIdentifier
        );
    }

    private resolveOnStartupOptions(
        inputOptions: Partial<ExperimentRunOptions>
    ): ExperimentRunOptions.AfterStartupResolution {
        return {
            ...inputOptions,
            loggerSeverity: inputOptions.loggerSeverity ?? SeverityLevel.INFO,
            logsFilePath: inputOptions.logsFilePath,

            datasetCacheUsage:
                inputOptions.datasetCacheUsage ??
                DatasetCacheUsageMode.NO_CACHE_USAGE,
            datasetCacheDirectoryPath:
                inputOptions.datasetCacheDirectoryPath ??
                CacheDirNames.defaultDatasetCacheDirectoryPath,
        };
    }

    private resolveAllExperimentRunOptions(
        optionsAfterStartupResolution: ExperimentRunOptions.AfterStartupResolution,
        requestedTargets: DatasetInputTargets
    ): ExperimentRunOptions {
        return {
            loggerSeverity: optionsAfterStartupResolution.loggerSeverity,
            logsFilePath: optionsAfterStartupResolution.logsFilePath,

            datasetCacheUsage: optionsAfterStartupResolution.datasetCacheUsage,
            datasetCacheDirectoryPath:
                optionsAfterStartupResolution.datasetCacheDirectoryPath,

            maxActiveSubprocessesNumber: Math.max(
                optionsAfterStartupResolution.maxActiveSubprocessesNumber ??
                    requestedTargets.workspacesNumber(),
                1
            ),
            maxParallelGenerationRequestsToModel:
                optionsAfterStartupResolution.maxParallelGenerationRequestsToModel ??
                1,

            buildAndParseCoqProjectSubprocessTimeoutMillis:
                optionsAfterStartupResolution.buildAndParseCoqProjectSubprocessTimeoutMillis,
            checkProofsSubprocessTimeoutMillis:
                optionsAfterStartupResolution.checkProofsSubprocessTimeoutMillis,

            enableSubprocessLifetimeDebugLogs:
                optionsAfterStartupResolution.enableSubprocessLifetimeDebugLogs ??
                false,

            enableSubprocessesSchedulingDebugLogs:
                optionsAfterStartupResolution.enableSubprocessesSchedulingDebugLogs ??
                false,
            enableModelsSchedulingDebugLogs:
                optionsAfterStartupResolution.enableModelsSchedulingDebugLogs ??
                false,
        };
    }
}

interface ExecutionContext {
    requestedTargets: DatasetInputTargets;
    resolvedRunOptions: ExperimentRunOptions;
    subprocessesScheduler: AsyncScheduler;
    logger: BenchmarkingLogger;
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
