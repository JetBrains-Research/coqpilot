import { ConfigurationError } from "../../../../llm/llmServiceErrors";
import { millisToString } from "../../../../llm/llmServices/utils/time";

import { CoqProofChecker } from "../../../../core/coqProofChecker";

import { stringifyAnyValue } from "../../../../utils/printers";
import { BenchmarkingLogger } from "../logging/benchmarkingLogger";
import { heavyCheckMark, heavyCrossMark } from "../logging/specialSymbols";
import { benchmarkedItemToJson } from "../reportBuilders/toJson";
import {
    BenchmarkedCompletionGeneration,
    BenchmarkedItem,
    CompletionGenerationFailureType,
    FailedCompletionGeneration,
    SuccessfulCompletionGeneration,
} from "../structures/benchmarkedItem";
import { BenchmarkingItem } from "../structures/benchmarkingItem";
import { writeToFile } from "../utils/fsUtils";
import { selectLLMServiceBuilder } from "../utils/llmServicesUtils";

import { benchmarkSingleCompletionGeneration } from "./benchmarkSingleCompletionGeneration";
import { TimeMark } from "./measureUtils";

export async function executeBenchmarkingTask(
    benchmarkingItem: BenchmarkingItem,
    saveToFilePath: string,
    itemLogger: BenchmarkingLogger
): Promise<BenchmarkedItem | undefined> {
    const task = benchmarkingItem.task;
    const params = benchmarkingItem.params;
    const llmService = selectLLMServiceBuilder(
        benchmarkingItem.llmServiceIdentifier
    )();
    try {
        const totalTime = new TimeMark();
        const result = await benchmarkSingleCompletionGeneration(
            task.getCompletionContext(),
            task.getSourceFileEnvironment(),
            params,
            llmService,
            // TODO: each coq proof checker should use its own prefix to work good in parallel (many checkers for the same theorem in the same file)
            new CoqProofChecker(task.preparedEnvironment.coqLspClient),
            itemLogger
        );
        logResult(result, totalTime.measureElapsedMillis(), itemLogger);

        const benchmarkedItem: BenchmarkedItem = {
            item: benchmarkingItem,
            result: result,
        };
        saveResultToFile(benchmarkedItem, saveToFilePath, itemLogger);

        return benchmarkedItem;
    } catch (e) {
        if (e instanceof ConfigurationError) {
            itemLogger
                .asOneRecord()
                .error(
                    `"${params.modelParams.modelId}" is configured incorrectly: ${e.message}`
                )
                .error("therefore, this benchmarking item will be skipped");
        } else {
            const loggedErrorMessage =
                e instanceof Error
                    ? e.stack !== undefined
                        ? e.stack
                        : `${e.name}: ${e.message}`
                    : stringifyAnyValue(e);
            itemLogger
                .asOneRecord()
                .error(`Unexpected error occurred:`)
                .error(loggedErrorMessage, "gray")
                .error("Therefore, this benchmarking item will be skipped");
        }
        return undefined;
    } finally {
        llmService.dispose();
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
    totalElapsedTimeMillis: number,
    itemLogger: BenchmarkingLogger
) {
    const success = result as SuccessfulCompletionGeneration;
    if (success !== null) {
        itemLogger
            .asOneRecord()
            .info(`Goal was succefully proven ${heavyCheckMark}`, "green")
            .debug("First valid proof:")
            .debug(`${success.validProofs[0]}`)
            .debug(
                `Total elapsed time: ${millisToString(totalElapsedTimeMillis)}`
            );
        return;
    }
    const failure = result as FailedCompletionGeneration;
    if (failure !== null) {
        let failureMessage: string;
        let logCause: boolean = true;
        switch (failure.failureType) {
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
            asOneRecordLogs.debug(`Cause: ${failure.causeMessage}`);
        }
        asOneRecordLogs.debug(
            `Total elapsed time: ${millisToString(totalElapsedTimeMillis)}`
        );
    }
    itemLogger.error(
        `Got unknown \`BenchmarkedCompletionGeneration\` type: ${stringifyAnyValue(result)}`
    );
}
