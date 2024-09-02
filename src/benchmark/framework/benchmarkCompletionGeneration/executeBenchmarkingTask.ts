import { ConfigurationError } from "../../../llm/llmServiceErrors";
import { millisToString } from "../../../llm/llmServices/utils/time";

import { stringifyAnyValue } from "../../../utils/printers";
import { BenchmarkingLogger } from "../logging/benchmarkingLogger";
import { heavyCheckMark, heavyCrossMark } from "../logging/specialSymbols";
import { benchmarkedItemToJson } from "../reportBuilders/toJson";
import { BenchmarkingItem } from "../structures/benchmarkingCore/benchmarkingItem";
import {
    BenchmarkedCompletionGeneration,
    BenchmarkedItem,
    CompletionGenerationFailureType,
    isFailedGeneration,
    isSuccessfulGeneration,
} from "../structures/benchmarkingResults/benchmarkedItem";
import { AsyncScheduler } from "../utils/asyncScheduler";
import { writeToFile } from "../utils/fsUtils";
import { selectLLMServiceBuilder } from "../utils/llmServicesUtils";

import { benchmarkSingleCompletionGeneration } from "./benchmarkSingleCompletionGeneration";
import { AbstractProofsChecker } from "./proofsCheckers/abstractProofsChecker";

export async function executeBenchmarkingTask(
    benchmarkingItem: BenchmarkingItem,
    saveToFilePath: string,
    itemLogger: BenchmarkingLogger,
    modelsScheduler: AsyncScheduler,
    proofsChecker: AbstractProofsChecker
): Promise<BenchmarkedItem | undefined> {
    const task = benchmarkingItem.task;
    const params = benchmarkingItem.params;
    const [llmService, llmServiceEventLogger] = selectLLMServiceBuilder(
        benchmarkingItem.params.llmServiceIdentifier
    )();
    task.parsedSourceFileData;
    try {
        const generationArgs = {
            completionContext: task.getCompletionContext(),
            sourceFileEnvironment: task.getSourceFileEnvironment(),
            benchmarkingModelParams: params,
            llmService: llmService,
            llmServiceEventLogger: llmServiceEventLogger,
            parsedSourceFileData: task.parsedSourceFileData,
            workspaceRoot: task.workspaceRoot,
        };
        const result = await benchmarkSingleCompletionGeneration(
            generationArgs,
            modelsScheduler,
            itemLogger,
            proofsChecker
        );
        logResult(result, itemLogger);

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
