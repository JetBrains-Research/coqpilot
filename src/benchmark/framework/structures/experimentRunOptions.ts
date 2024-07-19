import { SeverityLevel } from "../logging/benchmarkingLogger";

export interface ExperimentRunOptions {
    loggerSeverity: SeverityLevel;
    /**
     * Path relative to the root directory. If it set, logs will be written to this file.
     * Otherwise, they will be shown in the console.
     */
    logsFilePath: string | undefined;

    maxActiveSubprocessesNumber: number;
    maxParallelGenerationRequestsToModel: number;

    buildAndParseCoqProjectSubprocessTimeoutMillis: number | undefined;
    checkProofsSubprocessTimeoutMillis: number | undefined;

    enableSubprocessLifetimeDebugLogs: boolean;

    enableSubprocessesSchedulingDebugLogs: boolean;
    enableModelsSchedulingDebugLogs: boolean;
}
