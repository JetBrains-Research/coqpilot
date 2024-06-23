import { SeverityLevel } from "../logging/benchmarkingLogger";

export interface ExperimentRunOptions {
    loggerSeverity: SeverityLevel;
    maxActiveSubprocessesNumber: number;
    buildAndParseCoqProjectSubprocessTimeoutMillis: number | undefined;
    checkProofsSubprocessTimeoutMillis: number | undefined;
    enableSubprocessLifetimeDebugLogs: boolean;
    enableSchedulingDebugLogs: boolean;
}
