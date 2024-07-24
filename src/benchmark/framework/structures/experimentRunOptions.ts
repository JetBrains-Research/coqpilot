import { SeverityLevel } from "../logging/benchmarkingLogger";

import { DatasetCacheUsageMode } from "./datasetCaching";

export interface ExperimentRunOptions {
    loggerSeverity: SeverityLevel;
    /**
     * Path relative to the root directory. If it set, logs will be written to this file.
     * Otherwise, they will be shown in the console.
     */
    logsFilePath: string | undefined;

    datasetCacheUsage: DatasetCacheUsageMode;
    /**
     * Path relative to the root directory. If it is not set, a `dataset/.parsingCache` will be used.
     * Inside the cached dataset projects are stored: for a project `dataset/example`,
     * its cache might be found inside `${datasetCacheDirectoryPath}/example`.
     *
     * Note: the benchmarking framework is allowed to modify `datasetCacheDirectoryPath` content
     * if the corresponding `datasetCacheUsage` mode is enabled.
     */
    datasetCacheDirectoryPath: string | undefined;

    maxActiveSubprocessesNumber: number;
    maxParallelGenerationRequestsToModel: number;

    buildAndParseCoqProjectSubprocessTimeoutMillis: number | undefined;
    checkProofsSubprocessTimeoutMillis: number | undefined;

    enableSubprocessLifetimeDebugLogs: boolean;

    enableSubprocessesSchedulingDebugLogs: boolean;
    enableModelsSchedulingDebugLogs: boolean;
}
