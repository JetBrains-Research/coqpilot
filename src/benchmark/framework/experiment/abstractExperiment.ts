import { benchmark } from "../benchmarkingCore/benchmark";
import { TimeMark } from "../benchmarkingCore/singleCompletionGeneration/measureUtils";
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

import { LightweightSerializer } from "./lightweightItems/lightweightSerializer";
import {
    CacheTargetsImpl,
    DatasetCacheBuildingImpl,
} from "./setupDSL/datasetCacheBuilder";

export interface ExecutionContext {
    requestedTargets: DatasetInputTargets;
    resolvedRunOptions: ExperimentRunOptions;
    subprocessesScheduler: AsyncScheduler;
    logger: BenchmarkingLogger;
}

namespace CacheDirNames {
    export const defaultDatasetCacheDirectoryPath = "dataset/.parsingCache/";
}

export abstract class AbstractExperiment {
    constructor(
        private readonly bundles: InputBenchmarkingBundle[] = [],
        private sharedRunOptions: Partial<ExperimentRunOptions> = {}
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
            executionContext.logger,
            this.setupCoqProjectParser(executionContext)
        );
    }

    /**
     * Builds lightweight benchmarking items for the requested targets and saves them into `outputDirectoryPath`.
     * The returning promise resolves successfully if and only if the operation succeeded.
     *
     * *Warning:* `outputDirectoryPath` content will be cleared before saving the built lightweight benchmarking items.
     *
     * This operation is used as the first step for the large-scale benchmarking pipeline executed in TeamCity.
     * The goal is to resolve input for the benchmarks (specified via the setup DSL) into **separate** benchmarking items
     * that can be stored in the repository **efficiently**.
     *
     * The output `outputDirectoryPath` will have the following structure after the operation is successfully finished:
     * - `projects` subfolder: `[workspace path descriptor].json` files with `LightweightWorkspaceRoot` objects;
     * - `models` subfolder: `[modelId].json` files with `InputBenchmarkingModelParams.Params` objects;
     * - `items` subfolder: `[task descriptor].json` files with `LightweightBenchmarkingItem` objects.
     *
     * *Note on the efficiency of the operation.*
     * Unfortunately, calling this operation requires the requested dataset projects being built,
     * even though the next pipeline step (executed remotely) will need to build them again. However:
     * 1. The key importance of the `buildLightweightBenchmarkingItems` is to prepare *separate* benchmarking items:
     *    that requires parsing source files, for example, to find all requested admits. Thus, this step could not be ommitted.
     * 2. In practice, projects building and parsing can be skipped in case of dataset cache being present.
     *    Therefore, building dataset projects should be done only once locally and then reused with no overhead.
     *
     * *Implementation note*. So far this method simply builds the complete benchmarking items the same way as it is done
     * in the core `AbstractExperiment.run(...)` method and then serializes them in their lightweight versions.
     * Although the "unneccesary" model parameters resolution takes place ("unneccessary", because the models
     * will be saved unresolved for the sake of data storage efficiency), it actually validates the parameters specified by a user,
     * preventing such errors from being propagated to the large-scale pipeline itself.
     *
     * @param outputDirectoryPath a directory path relative to the root directory to save lightweight serialization into.
     */
    // TODO: clear-output-dir parameter
    // TODO: move this method to TeamCityExperiment
    async buildLightweightBenchmarkingItems(outputDirectoryPath: string) {
        const executionContext = this.prepareExecutionContext(
            this.sharedRunOptions,
            "[Building Lightweight Benchmarking Items]",
            (logger) => mergeAndResolveRequestedTargets(this.bundles, logger)
        );
        const benchmarkingItems =
            await this.buildBenchmarkingItems(executionContext);

        const serialization = LightweightSerializer.serializeToLightweight(
            benchmarkingItems,
            this.bundles
        );
        LightweightSerializer.logSerialization(
            serialization,
            executionContext.logger
        );
        LightweightSerializer.saveSerializationToDirectory(
            serialization,
            outputDirectoryPath,
            executionContext.logger
        );
    }

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
        const executionContext = this.prepareExecutionContext(
            {
                ...this.sharedRunOptions,
                ...runOptions,
            },
            "[Benchmarking]", // TODO: customize through run options
            (logger) => mergeAndResolveRequestedTargets(this.bundles, logger)
        );
        const totalTime = new TimeMark();

        const benchmarkingItems =
            await this.buildBenchmarkingItems(executionContext);

        // Since `AbstractExperiment.run(...)` is not always called with `await`,
        // this one might help triggering the expected behaviour
        return await this.executeBenchmarkingItems(
            benchmarkingItems,
            artifactsDirPath,
            executionContext,
            totalTime
        );
    }

    private async buildBenchmarkingItems(
        executionContext: ExecutionContext
    ): Promise<BenchmarkingItem[]> {
        const benchmarkingItems = await parseDatasetForBenchmarkingItems(
            this.bundles,
            executionContext.requestedTargets,
            executionContext.resolvedRunOptions,
            executionContext.logger,
            this.setupCoqProjectParser(executionContext)
        );
        if (benchmarkingItems.length === 0) {
            throw Error(
                "No items to benchmark: make sure the experiment input is configured correctly."
            );
        }
        return benchmarkingItems;
    }

    private async executeBenchmarkingItems(
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

        const executionContext: ExecutionContext = {
            requestedTargets: requestedTargets,
            resolvedRunOptions: resolvedRunOptions,
            subprocessesScheduler: subprocessesScheduler,
            logger: logger,
        };
        this.validateExecutionContextOrThrow(executionContext);

        return executionContext;
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

            failFast: optionsAfterStartupResolution.failFast ?? false,
            logFailFastTasksAborting:
                optionsAfterStartupResolution.logFailFastTasksAborting ?? false,
            proofGenerationRetries:
                optionsAfterStartupResolution.proofGenerationRetries,
            logTeamCityStatistics:
                optionsAfterStartupResolution.logTeamCityStatistics ?? false,
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
