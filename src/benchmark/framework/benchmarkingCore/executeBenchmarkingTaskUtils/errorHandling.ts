import { ConfigurationError } from "../../../../llm/llmServiceErrors";
import { ModelParams } from "../../../../llm/llmServices/modelParams";

import {
    buildErrorCompleteLog,
    wrapAsIllegalState,
} from "../../../../utils/errorsUtils";
import { IllegalStateError, unreachable } from "../../../../utils/throwErrors";
import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { BenchmarkingModelParams } from "../../structures/benchmarkingCore/benchmarkingModelParams";
import { BenchmarkingOptions } from "../../structures/benchmarkingCore/benchmarkingOptions";
import { AbortError } from "../../utils/asyncUtils/abortUtils";
import { BenchmarkingError } from "../../utils/throwErrors";

export namespace ExecuteBenchmarkingTaskErrorHandlingUtils {
    export type ExpectedError =
        | AbortError
        | BenchmarkingError
        | ConfigurationError
        | IllegalStateError;

    export function isExpectedError(e: any): e is ExpectedError {
        return (
            e instanceof AbortError ||
            e instanceof BenchmarkingError ||
            e instanceof ConfigurationError ||
            e instanceof IllegalStateError
        );
    }

    export function wrapUnexpectedErrorAsIllegalState(e: any): ExpectedError {
        return isExpectedError(e)
            ? e
            : wrapAsIllegalState(e, "unexpected error occurred");
    }

    export function logErrorIfNeeded(
        wrappedError: ExpectedError,
        itemLogger: BenchmarkingLogger,
        params: BenchmarkingModelParams<ModelParams>,
        options: BenchmarkingOptions,
        abortSignal: AbortSignal
    ) {
        if (wrappedError instanceof AbortError) {
            // Report `AbortError` only if requested
            if (options.logAbortingTasks) {
                itemLogger.debug(wrappedError.message);
            }
        } else {
            /**
             * Try to pollute logs less with the latecomers-errors:
             * if the first error has already occurred, just finish faster.
             * *Note:* Without synchronization, this code does not guarantee
             * that only the first error will be logged. However, it definitely
             * reduces the number of unnecessary error messages.
             */
            const doNotLogErrorAfterAbort =
                abortSignal.aborted && !options.logAbortingTasks;

            if (!doNotLogErrorAfterAbort) {
                logCommonError(
                    wrappedError,
                    itemLogger,
                    params,
                    options,
                    abortSignal
                );
            }
        }
    }

    function logCommonError(
        error: BenchmarkingError | ConfigurationError | IllegalStateError,
        itemLogger: BenchmarkingLogger,
        params: BenchmarkingModelParams<ModelParams>,
        options: BenchmarkingOptions,
        abortSignal: AbortSignal
    ) {
        const errorRecordLogger = itemLogger.asOneRecord();

        // log error by itself
        if (error instanceof BenchmarkingError) {
            errorRecordLogger.error(error.message);
        } else if (error instanceof ConfigurationError) {
            errorRecordLogger.error(
                `"${params.modelParams.modelId}" is configured incorrectly: ${error.message}`
            );
        } else if (error instanceof IllegalStateError) {
            errorRecordLogger
                .error(`Illegal state error occurred`)
                .error(buildErrorCompleteLog(error), "gray");
        } else {
            unreachable(
                "unexpected error type\n",
                buildErrorCompleteLog(error)
            );
        }

        // log conclusion
        if (abortSignal.aborted) {
            errorRecordLogger.info(
                "Benchmarking pipeline has been already aborted"
            );
            return;
        }
        if (options.failFast || error instanceof IllegalStateError) {
            const explanation = options.failFast
                ? "`failFast` strategy is enabled"
                : "internal invariants violated";
            errorRecordLogger.error(
                `Therefore, the benchmarking pipeline will be aborted: ${explanation}`
            );
        } else {
            errorRecordLogger.error(
                "Therefore, this benchmarking item will be skipped"
            );
        }
    }
}
