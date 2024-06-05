import { SeverityLevel } from "../logging/benchmarkingLogger";

export interface ExperimentRunOptions {
    loggerSeverity: SeverityLevel;
    maxActiveSubprocessesNumber: number;
    checkProofsSubprocessTimeoutMillis: number | undefined;
    enableSubprocessLifetimeDebugLogs: boolean;
    enableSchedulingDebugLogs: boolean;
}
