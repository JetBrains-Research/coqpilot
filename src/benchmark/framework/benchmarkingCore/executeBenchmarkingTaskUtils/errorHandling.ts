import { ConfigurationError } from "../../../../llm/llmServiceErrors";
import { ModelParams } from "../../../../llm/llmServices/modelParams";

import { buildErrorCompleteLog } from "../../../../utils/errorsUtils";
import { IllegalStateError } from "../../../../utils/throwErrors";
import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { BenchmarkingModelParams } from "../../structures/benchmarkingCore/benchmarkingModelParams";
import { BenchmarkingOptions } from "../../structures/benchmarkingCore/benchmarkingOptions";
import { FailFastAbortError } from "../../utils/asyncUtils/abortUtils";
import { BenchmarkingError } from "../../utils/throwErrors";

export namespace ExecuteBenchmarkingTaskErrorHandlingUtils {
    export type ExpectedError =
        | FailFastAbortError
        | BenchmarkingError
        | ConfigurationError
        | IllegalStateError;

    export function isExpectedError(e: any): e is ExpectedError {
        return (
            e instanceof FailFastAbortError ||
            e instanceof BenchmarkingError ||
            e instanceof ConfigurationError ||
            e instanceof IllegalStateError
        );
    }

    /**
     * Try to pollute logs less with the latecomers-errors:
     * if the first error has already occurred, just finish faster.
     * *Note:* Without synchronization, this code does not guarantee
     * that only the first error will be logged. However, it definitely
     * reduces the number of unnecessary error messages.
     */
    export function logAndRethrowFailFastError(
        error: ExpectedError,
        itemLogger: BenchmarkingLogger,
        params: BenchmarkingModelParams<ModelParams>,
        options: BenchmarkingOptions,
        abortSignal: AbortSignal
    ): never {
        const logError = (e: any) =>
            logCommonError(e, itemLogger, params, options, abortSignal);

        // Handle "abort error" separately: report it only if requested
        if (error instanceof FailFastAbortError) {
            if (options.logFailFastTasksAborting) {
                itemLogger.debug(error.message);
            }
            throw error;
        }
        if (abortSignal.aborted) {
            // If benchmarks are already aborted, further errors should not be reported,
            // unless it was asked by a user
            if (options.logFailFastTasksAborting) {
                logError(error);
            }
        } else {
            // This task is one of the first tasks failing; they will cause fail-fast abort soon
            logError(error);
        }
        // In the fail-fast mode the errors of the tasks are always rethrown,
        // so to reject their `Promise`-s
        throw error;
    }

    export function wrapUnexpectedErrorAsIllegalState(
        e: any
    ): [ExpectedError, boolean] {
        if (!isExpectedError(e)) {
            return [
                new IllegalStateError(
                    `unexpected error occurred:\n${buildErrorCompleteLog(e)}`
                ),
                true,
            ];
        }
        return [e, false];
    }

    export function logCommonError(
        e: ExpectedError,
        itemLogger: BenchmarkingLogger,
        params: BenchmarkingModelParams<ModelParams>,
        options: BenchmarkingOptions,
        abortSignal: AbortSignal
    ) {
        const errorRecordLogger = itemLogger.asOneRecord();
        const logConclusion = () => {
            if (options.failFast) {
                if (abortSignal.aborted) {
                    errorRecordLogger.info(
                        "Benchmarking pipeline has been already aborted (`failFast` strategy is enabled)"
                    );
                } else {
                    errorRecordLogger.error(
                        "Therefore, the benchmarking pipeline will be aborted (`failFast` strategy is enabled)"
                    );
                }
            } else {
                errorRecordLogger.error(
                    "Therefore, this benchmarking item will be skipped"
                );
            }
        };

        if (e instanceof BenchmarkingError) {
            errorRecordLogger.error(e.message);
        } else if (e instanceof ConfigurationError) {
            errorRecordLogger.error(
                `"${params.modelParams.modelId}" is configured incorrectly: ${e.message}`
            );
        } else {
            errorRecordLogger
                .error(`Error occurred:`)
                .error(buildErrorCompleteLog(e), "gray");
        }
        logConclusion();
    }
}
