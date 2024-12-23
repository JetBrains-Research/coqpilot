import { ConfigurationError } from "../../../llm/llmServiceErrors";
import { ModelParams } from "../../../llm/llmServices/modelParams";

import { buildErrorCompleteLog } from "../../../utils/errorsUtils";
import { stringifyAnyValue } from "../../../utils/printers";
import { millisToString } from "../../../utils/time";
import {
    AsOneRecordLogsBuilder,
    BenchmarkingLogger,
} from "../logging/benchmarkingLogger";
import { heavyCheckMark, heavyCrossMark } from "../logging/specialSymbols";
import { benchmarkedItemToJson } from "../reportBuilders/toJson";
import { BenchmarkingItem } from "../structures/benchmarkingCore/benchmarkingItem";
import { BenchmarkingModelParams } from "../structures/benchmarkingCore/benchmarkingModelParams";
import { BenchmarkingOptions } from "../structures/benchmarkingCore/benchmarkingOptions";
import {
    BenchmarkedCompletionGeneration,
    BenchmarkedItem,
    CompletionGenerationFailureType,
    isFailedGeneration,
    isSuccessfulGeneration,
} from "../structures/benchmarkingResults/benchmarkedItem";
import {
    FailFastAbortError,
    throwOnAbort,
} from "../utils/asyncUtils/abortUtils";
import { AsyncScheduler } from "../utils/asyncUtils/asyncScheduler";
import { selectLLMServiceBuilder } from "../utils/commonStructuresUtils/llmServicesUtils";
import { writeToFile } from "../utils/fileUtils/fs";

import { benchmarkSingleCompletionGeneration } from "./singleCompletionGeneration/benchmarkSingleCompletionGeneration";
import { AbstractProofsChecker } from "./singleCompletionGeneration/proofsCheckers/abstractProofsChecker";

export async function executeBenchmarkingTask(
    benchmarkingItem: BenchmarkingItem,
    saveToFilePath: string,
    options: BenchmarkingOptions,
    itemLogger: BenchmarkingLogger,
    modelsScheduler: AsyncScheduler,
    proofsChecker: AbstractProofsChecker,
    abortSignal: AbortSignal
): Promise<BenchmarkedItem | undefined> {
    const task = benchmarkingItem.task;
    const params = benchmarkingItem.params;
    const [llmService, llmServiceEventLogger] = selectLLMServiceBuilder(
        benchmarkingItem.params.llmServiceIdentifier
    )();
    const logError = (e: any) =>
        logCommonError(e, itemLogger, params, options, abortSignal);

    try {
        const generationArgs = {
            completionContext: task.getCompletionContext(),
            sourceTheorem: task.sourceTheorem,
            sourceFileEnvironment: task.getSourceFileEnvironment(),
            benchmarkingModelParams: params,
            llmService: llmService,
            llmServiceEventLogger: llmServiceEventLogger,
            parsedSourceFileData: task.parsedSourceFileData,
            workspaceRoot: task.workspaceRoot,
        };
        throwOnAbort(abortSignal);
        const result = await benchmarkSingleCompletionGeneration(
            generationArgs,
            options,
            modelsScheduler,
            itemLogger,
            proofsChecker,
            abortSignal
        );
        logResult(result, itemLogger);

        const benchmarkedItem: BenchmarkedItem = {
            item: benchmarkingItem,
            result: result,
        };
        saveResultToFile(benchmarkedItem, saveToFilePath, itemLogger);

        return benchmarkedItem;
    } catch (e) {
        if (options.failFast) {
            /*
             * Try to pollute logs less with the latecomers-errors:
             * if the first error has already occurred, just finish faster.
             * *Note:* Without synchronization, this code does not guarantee
             * that only the first error will be logged. However, it definitely
             * reduces the number of unnecessary error messages.
             */

            // Handle "abort error" separately: report it only if requested
            if (e instanceof FailFastAbortError) {
                if (options.logFailFastTasksAborting) {
                    itemLogger.debug(e.message);
                }
                throw e;
            }
            if (abortSignal.aborted) {
                // If benchmarks are already aborted, further errors should not be reported,
                // unless it was asked by a user
                if (options.logFailFastTasksAborting) {
                    logError(e);
                }
            } else {
                // This task is one of the first tasks failing; they will cause fail-fast abort soon
                logError(e);
            }
            // In the fail-fast mode the errors of the tasks are always rethrown,
            // so to reject their `Promise`-s
            throw e;
        } else {
            logError(e);
            return undefined;
        }
    } finally {
        llmService.dispose();
    }
}

function logCommonError(
    e: any,
    itemLogger: BenchmarkingLogger,
    params: BenchmarkingModelParams<ModelParams>,
    options: BenchmarkingOptions,
    abortSignal: AbortSignal
) {
    const logConclusion = (errorRecordLogger: AsOneRecordLogsBuilder) => {
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

    if (e instanceof ConfigurationError) {
        logConclusion(
            itemLogger
                .asOneRecord()
                .error(
                    `"${params.modelParams.modelId}" is configured incorrectly: ${e.message}`
                )
        );
    } else {
        logConclusion(
            itemLogger
                .asOneRecord()
                .error(`Error occurred:`)
                .error(buildErrorCompleteLog(e), "gray")
        );
    }
}

function saveResultToFile(
    benchmarkedItem: BenchmarkedItem,
    filePath: string,
    itemLogger: BenchmarkingLogger
) {
    writeToFile(benchmarkedItemToJson(benchmarkedItem), filePath, (e) =>
        itemLogger
            .asOneRecord()
            .error(`Failed to save results into ${filePath}`)
            .debug(`Cause: ${stringifyAnyValue(e)}`)
    );
}

function logResult(
    result: BenchmarkedCompletionGeneration,
    itemLogger: BenchmarkingLogger
) {
    if (isSuccessfulGeneration(result)) {
        itemLogger
            .asOneRecord()
            .info(`Goal was succefully proven ${heavyCheckMark}`, "green")
            .debug("First valid proof:")
            .debug(`${result.validProofs[0].asString}`)
            .debug(
                `Total effective elapsed time: ${millisToString(result.elapsedTime.totalMillis)}`
            );
    } else if (isFailedGeneration(result)) {
        let failureMessage: string;
        let logCause: boolean = true;
        switch (result.failureType) {
            case CompletionGenerationFailureType.SEARCH_FAILED:
                failureMessage = "Valid proofs not found";
                logCause = false;
                break;
            case CompletionGenerationFailureType.COQ_PROOF_CHECKER_ERROR:
                failureMessage = "`CoqProofChecker` error";
                break;
            case CompletionGenerationFailureType.TIMEOUT:
                failureMessage = "Proof validation timeout";
                break;
        }
        const asOneRecordLogs = itemLogger
            .asOneRecord()
            .info(`${failureMessage} ${heavyCrossMark}`, "red");
        if (logCause) {
            asOneRecordLogs.debug(`Cause: ${result.causeMessage}`);
        }
        asOneRecordLogs.debug(
            `Total effective elapsed time: ${millisToString(result.elapsedTime.totalMillis)}`
        );
    } else {
        itemLogger.error(
            `Got unknown \`BenchmarkedCompletionGeneration\` type: ${stringifyAnyValue(result)}`
        );
    }
}
