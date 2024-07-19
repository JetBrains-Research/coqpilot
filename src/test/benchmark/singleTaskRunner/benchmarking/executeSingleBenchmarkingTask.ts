import { ConfigurationError } from "../../../../llm/llmServiceErrors";
import { millisToString } from "../../../../llm/llmServices/utils/time";

import { performAndMeasureCompletionGeneration } from "../core/performCompletionGeneration";

import { BenchmarkingLogger } from "../../../../benchmark/framework/logging/benchmarkingLogger";
import {
    heavyCheckMark,
    heavyCrossMark,
} from "../../../../benchmark/framework/logging/specialSymbols";
import {
    BenchmarkedCompletionGeneration,
    CompletionGenerationFailureType,
    isFailedGeneration,
    isSuccessfulGeneration,
} from "../../../../benchmark/framework/structures/benchmarkedItem";
import {
    createFileWithParentDirectories,
    writeToFile,
} from "../../../../benchmark/framework/utils/fsUtils";
import { selectLLMServiceBuilder } from "../../../../benchmark/framework/utils/llmServicesUtils";
import { stringifyAnyValue } from "../../../../utils/printers";
import { SingleTaskRunnerOptions } from "../runnerOptions";

import { SingleTaskRunnerStructures } from "./benchmarkingTask";

export namespace SingleTaskRunner {
    export async function executeBenchmarkingTask(
        task: SingleTaskRunnerStructures.BenchmarkingTask,
        executionOptions: SingleTaskRunnerOptions.BenchmarkingTaskExecutionOptions,
        saveToFilePath: string,
        logger: BenchmarkingLogger
    ): Promise<BenchmarkedCompletionGeneration | undefined> {
        createFileWithParentDirectories("clear", saveToFilePath);

        const params = task.params;
        const llmService = selectLLMServiceBuilder(
            params.llmServiceIdentifier
        )();
        try {
            const result = await performAndMeasureCompletionGeneration(
                SingleTaskRunnerStructures.buildCompletionContext(task.target),
                SingleTaskRunnerStructures.buildSourceFileEnvironment(
                    task.parsedSourceFile
                ),
                params,
                llmService,
                task.workspaceRootDirectoryPath,
                executionOptions,
                logger
            );
            logResult(result, logger);
            saveResultToFile(result, saveToFilePath, logger);
            return result;
        } catch (e) {
            if (e instanceof ConfigurationError) {
                logger
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
                logger
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
                )
                .info("");
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

    function saveResultToFile(
        result: BenchmarkedCompletionGeneration,
        filePath: string,
        itemLogger: BenchmarkingLogger
    ) {
        writeToFile(resultToJson(result), filePath, (e) =>
            itemLogger
                .asOneRecord()
                .error(`Failed to save results into ${filePath}`)
                .debug(`Cause: ${stringifyAnyValue(e)}`)
        );
    }

    function resultToJson(result: BenchmarkedCompletionGeneration): string {
        return JSON.stringify(result, null, 2);
    }
}
