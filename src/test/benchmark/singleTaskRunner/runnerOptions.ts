import { SeverityLevel } from "../../../benchmark/framework/logging/benchmarkingLogger";

export namespace SingleTaskRunnerOptions {
    export interface RunnerOptions {
        saveResultToFilePath: string;

        loggerSeverity: SeverityLevel;
        /**
         * Path relative to the root directory. If it set, logs will be written to this file.
         * Otherwise, they will be shown in the console.
         */
        logsFilePath: string | undefined;

        execution: BenchmarkingTaskExecutionOptions;
    }

    export interface BenchmarkingTaskExecutionOptions {
        requestLLMServiceMaxRetries: number;
        proofsValidationTimeoutMillis: number;
    }
}
