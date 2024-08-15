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

namespace CacheDirNames {
    export const defaultDatasetCacheDirectoryPath = "dataset/.parsingCache/";
}

export class Experiment {
    private mergedRequestedTargets: DatasetInputTargets | undefined = undefined;

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
     * @param artifactsDirPath empty directory path relative to the root directory.
     * @param runOptions properties to update the options for **this** run with. To save the updated options for the further runs use `Experiment.updateRunOptions(...)` method instead.
     */
    async run(
        artifactsDirPath: string,
        runOptions: Partial<ExperimentRunOptions> = {}
    ): Promise<ExperimentResults> {
        const totalTime = new TimeMark();

        const thisRunOptions: Partial<ExperimentRunOptions> = {
            ...this.sharedRunOptions,
            ...runOptions,
        };
        const optionsAfterStartupResolution =
            this.resolveOnStartupOptions(thisRunOptions);
        const logger: BenchmarkingLogger = new BenchmarkingLoggerImpl(
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
            "[Benchmarking]" // TODO: customize through run options
        );

        this.mergedRequestedTargets = mergeAndResolveRequestedTargets(
            this.bundles,
            logger
        );
        const resolvedRunOptions = this.resolveAllExperimentRunOptions(
            optionsAfterStartupResolution
        );

        const subprocessesScheduler = new AsyncScheduler(
            resolvedRunOptions.maxActiveSubprocessesNumber,
            resolvedRunOptions.enableSubprocessesSchedulingDebugLogs,
            "Subprocesses Scheduler"
        );

        const benchmarkingItems = await parseDatasetForBenchmarkingItems(
            this.bundles,
            this.mergedRequestedTargets,
            resolvedRunOptions,
            subprocessesScheduler,
            logger
        );
        if (benchmarkingItems.length === 0) {
            throw Error(
                "No items to benchmark: make sure the experiment input is configured correctly."
            );
        }

        return benchmark(
            benchmarkingItems,
            resolveAsAbsolutePath(joinPaths(getRootDir(), artifactsDirPath)),
            resolvedRunOptions,
            subprocessesScheduler,
            logger,
            totalTime
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
        optionsAfterStartupResolution: ExperimentRunOptions.AfterStartupResolution
    ): ExperimentRunOptions {
        if (this.mergedRequestedTargets === undefined) {
            throw Error(
                "`mergedRequestedTargets` should be built before input options resolution"
            );
        }
        return {
            loggerSeverity: optionsAfterStartupResolution.loggerSeverity,
            logsFilePath: optionsAfterStartupResolution.logsFilePath,

            datasetCacheUsage: optionsAfterStartupResolution.datasetCacheUsage,
            datasetCacheDirectoryPath:
                optionsAfterStartupResolution.datasetCacheDirectoryPath,

            maxActiveSubprocessesNumber: Math.max(
                optionsAfterStartupResolution.maxActiveSubprocessesNumber ??
                    this.mergedRequestedTargets.workspacesNumber(),
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
