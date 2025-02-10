import { benchmark } from "../benchmarkingCore/benchmark";
import { TimeMark } from "../benchmarkingCore/singleCompletionGeneration/measureTimeUtils";
import { AbstractProofsChecker } from "../benchmarkingCore/singleCompletionGeneration/proofsCheckers/abstractProofsChecker";
import {
    BenchmarkingLogger,
    BenchmarkingLoggerImpl,
    SeverityLevel,
} from "../logging/benchmarkingLogger";
import { AbstractCoqProjectParser } from "../parseDataset/coqProjectParser/abstractCoqProjectParser";
import { parseDatasetForBenchmarkingItems } from "../parseDataset/core/parseDatasetForBenchmarkingItems";
import { BenchmarkingItem } from "../structures/benchmarkingCore/benchmarkingItem";
import { ExperimentResults } from "../structures/benchmarkingResults/experimentResults";
import {
    DatasetInputTargets,
    mergeInputTargets,
} from "../structures/common/inputTargets";
import { DatasetCacheUsageMode } from "../structures/inputParameters/datasetCaching";
import { ExperimentRunOptions } from "../structures/inputParameters/experimentRunOptions";
import { InputBenchmarkingBundle } from "../structures/inputParameters/inputBenchmarkingBundle";
import { AsyncScheduler } from "../utils/asyncUtils/asyncScheduler";
import {
    getRootDir,
    joinPaths,
    resolveAsAbsolutePath,
} from "../utils/fileUtils/fs";
import { throwBenchmarkingError } from "../utils/throwErrors";

import {
    CacheTargetsImpl,
    DatasetCacheBuildingImpl,
} from "./setupDSL/datasetCacheBuilder";

export interface ExecutionContext {
    requestedWorkspaces: string[];
    resolvedRunOptions: ExperimentRunOptions;
    subprocessesScheduler: AsyncScheduler;
    logger: BenchmarkingLogger;
}

namespace CacheDirNames {
    export const defaultDatasetCacheDirectoryPath = "dataset/.parsingCache/";
}

export abstract class AbstractExperiment {
    constructor(
        protected readonly bundles: InputBenchmarkingBundle[] = [],
        protected sharedRunOptions: Partial<ExperimentRunOptions> = {}
    ) {}

    protected abstract validateExecutionContextOrThrow(
        executionContext: ExecutionContext
    ): void;

    protected abstract setupCoqProjectParser: (
        executionContext: ExecutionContext
    ) => AbstractCoqProjectParser;

    protected abstract setupProofsChecker: (
        executionContext: ExecutionContext
    ) => AbstractProofsChecker;

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
        const [requestedTargets, executionContext] =
            this.prepareExecutionContextFromInputTargets(
                {
                    ...this.sharedRunOptions,
                    datasetCacheDirectoryPath: datasetCacheDirectoryPath,
                },
                "[Dataset Cache Building]",
                (logger) =>
                    CacheTargetsImpl.buildCacheTargets(
                        cacheTargetsBuilders,
                        logger
                    )
            );
        await DatasetCacheBuildingImpl.buildDatasetCache(
            requestedTargets,
            executionContext.resolvedRunOptions,
            executionContext.logger,
            this.setupCoqProjectParser(executionContext)
        );
    }

    // TODO: support absolute `artifactsDirPath`
    /**
     * The core method that executes the benchmarking experiment.
     *
     * @param artifactsDirPath empty directory path relative to the root directory.
     * @param runOptions properties to update the options for **this** run with. To save the updated options for the further runs use `AbstractExperiment.updateRunOptions(...)` method instead.
     */
    async run(
        artifactsDirPath: string,
        runOptions: Partial<ExperimentRunOptions> = {}
    ): Promise<ExperimentResults> {
        const [requestedTargets, executionContext] =
            this.prepareExecutionContextFromInputTargets(
                {
                    ...this.sharedRunOptions,
                    ...runOptions,
                },
                "[Benchmarking]", // TODO: customize through run options
                (logger) =>
                    AbstractExperiment.mergeAndResolveRequestedTargets(
                        this.bundles,
                        logger
                    )
            );
        const totalTime = new TimeMark();

        const benchmarkingItems = await this.buildBenchmarkingItems(
            requestedTargets,
            executionContext
        );

        // Since `AbstractExperiment.run(...)` is not always called with `await`,
        // this one might help triggering the expected behaviour
        return await this.executeBenchmarkingItems(
            benchmarkingItems,
            artifactsDirPath,
            executionContext,
            totalTime
        );
    }

    protected async buildBenchmarkingItems(
        requestedTargets: DatasetInputTargets,
        executionContext: ExecutionContext
    ): Promise<BenchmarkingItem[]> {
        const benchmarkingItems = await parseDatasetForBenchmarkingItems(
            this.bundles,
            requestedTargets,
            executionContext.resolvedRunOptions,
            executionContext.logger,
            this.setupCoqProjectParser(executionContext)
        );
        if (benchmarkingItems.length === 0) {
            throwBenchmarkingError(
                "No items to benchmark: make sure the experiment input is configured correctly"
            );
        }
        return benchmarkingItems;
    }

    protected async executeBenchmarkingItems(
        benchmarkingItems: BenchmarkingItem[],
        artifactsDirPath: string,
        executionContext: ExecutionContext,
        totalTime: TimeMark
    ): Promise<ExperimentResults> {
        return benchmark(
            benchmarkingItems,
            resolveAsAbsolutePath(joinPaths(getRootDir(), artifactsDirPath)),
            executionContext.resolvedRunOptions,
            executionContext.logger,
            totalTime,
            this.setupProofsChecker(executionContext)
        );
    }

    protected prepareExecutionContextFromInputTargets(
        runOptions: Partial<ExperimentRunOptions>,
        loggerIdentifier: string,
        buildRequestedTargets: (
            logger: BenchmarkingLogger
        ) => DatasetInputTargets
    ): [DatasetInputTargets, ExecutionContext] {
        return this.prepareExecutionContext(
            runOptions,
            loggerIdentifier,
            buildRequestedTargets,
            (requestedTargets) =>
                requestedTargets
                    .entries()
                    .map(([workspaceRoot, _]) => workspaceRoot.directoryPath)
        );
    }

    protected prepareExecutionContext<T>(
        runOptions: Partial<ExperimentRunOptions>,
        loggerIdentifier: string,
        prepareTargets: (logger: BenchmarkingLogger) => T,
        getRequestedWorkspaces: (preparedTargets: T) => string[]
    ): [T, ExecutionContext] {
        const optionsAfterStartupResolution =
            this.resolveOnStartupOptions(runOptions);
        const logger = this.initLogger(
            optionsAfterStartupResolution,
            loggerIdentifier
        );

        const preparedTargets = prepareTargets(logger);
        const requestedWorkspaces = getRequestedWorkspaces(preparedTargets);
        const resolvedRunOptions = this.resolveAllExperimentRunOptions(
            optionsAfterStartupResolution,
            requestedWorkspaces
        );

        const subprocessesScheduler = new AsyncScheduler(
            resolvedRunOptions.maxActiveSubprocessesNumber,
            resolvedRunOptions.enableSubprocessesSchedulingDebugLogs,
            "Subprocesses Scheduler"
        );

        const executionContext: ExecutionContext = {
            requestedWorkspaces: requestedWorkspaces,
            resolvedRunOptions: resolvedRunOptions,
            subprocessesScheduler: subprocessesScheduler,
            logger: logger,
        };
        this.validateExecutionContextOrThrow(executionContext);

        return [preparedTargets, executionContext];
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
        requestedWorkspaces: string[]
    ): ExperimentRunOptions {
        // So far `coqLspServerPath` is applied to the benchmarking system
        // by storing it into `process.env.COQ_LSP_PATH`.
        // TODO: pass it through the system explicitly (!)
        const customCoqLspServerPath =
            optionsAfterStartupResolution.coqLspServerPath;
        if (customCoqLspServerPath !== undefined) {
            process.env.COQ_LSP_PATH = customCoqLspServerPath;
        }

        return {
            loggerSeverity: optionsAfterStartupResolution.loggerSeverity,
            logsFilePath: optionsAfterStartupResolution.logsFilePath,

            coqLspServerPath: undefined, // TODO: is passed through `process.env.COQ_LSP_PATH` above

            datasetCacheUsage: optionsAfterStartupResolution.datasetCacheUsage,
            datasetCacheDirectoryPath:
                optionsAfterStartupResolution.datasetCacheDirectoryPath,

            maxActiveSubprocessesNumber: Math.max(
                optionsAfterStartupResolution.maxActiveSubprocessesNumber ??
                    requestedWorkspaces.length,
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

            failFast: optionsAfterStartupResolution.failFast ?? false,
            logFailFastTasksAborting:
                optionsAfterStartupResolution.logFailFastTasksAborting ?? false,
            proofGenerationRetries:
                optionsAfterStartupResolution.proofGenerationRetries,
            logTeamCityStatistics:
                optionsAfterStartupResolution.logTeamCityStatistics ?? false,
        };
    }

    protected static mergeAndResolveRequestedTargets(
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
}
