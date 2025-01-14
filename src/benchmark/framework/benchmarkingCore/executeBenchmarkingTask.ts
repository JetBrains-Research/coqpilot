import { ConfigurationError } from "../../../llm/llmServiceErrors";
import { ModelParams } from "../../../llm/llmServices/modelParams";

import { buildErrorCompleteLog } from "../../../utils/errorsUtils";
import { toFormattedJsonString } from "../../../utils/printers";
import { millisToString } from "../../../utils/time";
import {
    AsOneRecordLogsBuilder,
    BenchmarkingLogger,
} from "../logging/benchmarkingLogger";
import { heavyCheckMark, heavyCrossMark } from "../logging/specialSymbols";
import { BasicJsonSerialization } from "../reportBuilders/basicJson/serialization";
import { BenchmarkingItem } from "../structures/benchmarkingCore/benchmarkingItem";
import { BenchmarkingModelParams } from "../structures/benchmarkingCore/benchmarkingModelParams";
import { BenchmarkingOptions } from "../structures/benchmarkingCore/benchmarkingOptions";
import {
    BenchmarkedItem,
    BenchmarkingResult,
} from "../structures/benchmarkingResults/benchmarkedItem";
import {
    FailFastAbortError,
    throwOnAbort,
} from "../utils/asyncUtils/abortUtils";
import { AsyncScheduler } from "../utils/asyncUtils/asyncScheduler";
import { selectLLMServiceBuilder } from "../utils/commonStructuresUtils/llmServicesUtils";
import { buildSafeJsonFileName } from "../utils/fileUtils/fileNameUtils";
import {
    joinPaths,
    provideEmptyDirectoryOrThrow,
    saveToFileOrHandleError,
} from "../utils/fileUtils/fs";

import {
    ParentProofToFix,
    benchmarkSingleCompletionGeneration,
} from "./singleCompletionGeneration/benchmarkSingleCompletionGeneration";
import { AbstractProofsChecker } from "./singleCompletionGeneration/proofsCheckers/abstractProofsChecker";

namespace ArtifactsNames {
    export const benchmarkingItemFileName = "input-task.json";
    export const resultReportFileName = "result.json";
}

// TODO (mb): document multiround execution
export async function executeBenchmarkingTask(
    benchmarkingItem: BenchmarkingItem,
    saveToDirPath: string,
    options: BenchmarkingOptions,
    itemLogger: BenchmarkingLogger,
    modelsScheduler: AsyncScheduler,
    proofsChecker: AbstractProofsChecker,
    abortSignal: AbortSignal
): Promise<BenchmarkedItem | undefined> {
    provideEmptyDirectoryOrThrow(saveToDirPath, "item artifacts");
    saveInputTaskToFileOrThrow(
        benchmarkingItem,
        joinPaths(saveToDirPath, ArtifactsNames.benchmarkingItemFileName),
        itemLogger
    );

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
            parentProofToFix: undefined,
            nextGeneratedProofId: 0,
            round: 0,
            llmService: llmService,
            llmServiceEventLogger: llmServiceEventLogger,
            parsedSourceFileData: task.parsedSourceFileData,
            workspaceRoot: task.workspaceRoot,
        };

        async function benchmarkCompletionGenerationRound(
            parentProof: ParentProofToFix | undefined,
            nextGeneratedProofId: number,
            roundIndex: number
        ): Promise<BenchmarkingResult> {
            const thisRoundGenerationArgs = {
                ...generationArgs,
                parentProofToFix: parentProof,
                nextGeneratedProofId: nextGeneratedProofId,
                round: roundIndex,
            };
            const result = await benchmarkSingleCompletionGeneration(
                thisRoundGenerationArgs,
                options,
                modelsScheduler,
                itemLogger,
                proofsChecker,
                abortSignal
            );
            logResult(result, itemLogger);
            return result;
        }

        let rootResult: BenchmarkingResult | undefined = undefined;

        const maxRoundsNumber =
            params.modelParams.multiroundProfile.maxRoundsNumber;
        let curRoundProofsToFix: (ParentProofToFix | undefined)[] = [undefined];
        let nextGeneratedProofId = 0;

        for (let roundIndex = 0; roundIndex < maxRoundsNumber; roundIndex++) {
            throwOnAbort(abortSignal);
            const nextRoundProofsToFix: ParentProofToFix[] = [];
            for (const parentProof of curRoundProofsToFix) {
                const childRoundResult =
                    await benchmarkCompletionGenerationRound(
                        parentProof,
                        nextGeneratedProofId,
                        roundIndex
                    );
                nextGeneratedProofId += childRoundResult.generatedProofs.length;
                if (parentProof === undefined) {
                    // roundIndex === 0
                    rootResult = childRoundResult;
                } else {
                    parentProof.benchmarkedProof.linkNextRoundResult(
                        childRoundResult
                    );
                    childRoundResult.linkParentProofToFix(
                        parentProof.benchmarkedProof
                    );
                }
                saveRoundResultToFileOrThrow(
                    childRoundResult,
                    joinPaths(
                        saveToDirPath,
                        buildRoundResultFileName(
                            roundIndex,
                            parentProof?.benchmarkedProof.generatedProofId
                        )
                    ),
                    itemLogger
                );

                if (childRoundResult.isFailedToFinishRound()) {
                    /**
                     * There are different policies of what to do when one of the proof-fixing rounds has failed,
                     * but here the following is chosen: to return the benchmarking result "generally" failed to finish
                     * (meaning that `rootResult.hasFailedToFinish()` will return `true`),
                     * with some of the proofs not reaching the `maxRoundsNumber` fixes.
                     *
                     * This strategy seems most reasonable: since rounds may fail only because of coq-lsp or coq-proof-checker errors,
                     * such a failure will most likely not be fixed by itself in the current setup for this benchmarking task.
                     * Therefore, there is no much sense in trying to fix other proofs generating their new versions not being able to check them.
                     */
                    // TODO (mb): briefly add to the top-level description
                    break;
                }
                // assign non-valid generated proofs for regeneration on next rounds
                for (const nonValidProof of childRoundResult.thisRoundNonValidProofs) {
                    nextRoundProofsToFix.push({
                        benchmarkedProof: nonValidProof,
                        diagnostic: nonValidProof.diagnostic,
                    });
                }
            }
            curRoundProofsToFix = nextRoundProofsToFix;
        }

        const benchmarkedItem: BenchmarkedItem = {
            item: benchmarkingItem,
            result: rootResult!, // TODO (mb): handle !
        };
        saveResultToFile(
            benchmarkedItem.result,
            joinPaths(saveToDirPath, ArtifactsNames.resultReportFileName),
            itemLogger
        );

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

function saveInputTaskToFileOrThrow(
    benchmarkingItem: BenchmarkingItem,
    filePath: string,
    itemLogger: BenchmarkingLogger
) {
    return saveToFileOrHandleError(
        toFormattedJsonString(
            BasicJsonSerialization.serializeBenchmarkingItem(benchmarkingItem)
        ),
        filePath,
        itemLogger,
        "task final result",
        true
    );
}

function buildRoundResultFileName(
    round: number,
    parentProofToFixId: number | undefined
): string {
    const parentId =
        parentProofToFixId === undefined
            ? `generate-proofs`
            : `fix-proof-${parentProofToFixId}`;
    return buildSafeJsonFileName(`round-${round}-${parentId}`);
}

function saveRoundResultToFileOrThrow(
    roundResult: BenchmarkingResult,
    filePath: string,
    itemLogger: BenchmarkingLogger
) {
    return saveToFileOrHandleError(
        toFormattedJsonString(
            BasicJsonSerialization.serializeBenchmarkingResultAsSingleRound(
                roundResult
            )
        ),
        filePath,
        itemLogger,
        `round result`,
        true
    );
}

function saveResultToFile(
    rootResult: BenchmarkingResult,
    filePath: string,
    itemLogger: BenchmarkingLogger
) {
    return saveToFileOrHandleError(
        toFormattedJsonString(
            BasicJsonSerialization.serializeBenchmarkingResultAsRoundsTree(
                rootResult
            )
        ),
        filePath,
        itemLogger,
        "task final result",
        false
    );
}

function logResult(result: BenchmarkingResult, itemLogger: BenchmarkingLogger) {
    if (result.isSuccessfulCompletion()) {
        // TODO (mb): log round info
        itemLogger
            .asOneRecord()
            .info(`Goal was succefully proven ${heavyCheckMark}`, "green")
            .debug("First valid proof:")
            .debug(`${result.getAllValidProofs()[0].asString}`)
            .debug(
                `Total effective elapsed time: ${millisToString(result.elapsedTime.totalMillis)}`
            );
    } else {
        let failureMessage: string;
        let cause: string | undefined = undefined;
        if (result.hasSuccessfullyFinished()) {
            failureMessage = "Valid proofs not found";
        } else {
            const allFailedRounds = result.getAllFailedToFinishRounds();
            // TODO (mb): log all rounds failed just in case
            const firstFailedRound = allFailedRounds[0];
            switch (firstFailedRound.failureMetadata.failureType) {
                case "COQ_LSP_TIMEOUT":
                    failureMessage = "Proof validation timeout";
                    break;
                case "COQ_PROOF_CHECKER_ERROR":
                    failureMessage = "`CoqProofChecker` error";
                    break;
            }
            cause = firstFailedRound.failureMetadata.causeMessage;
        }

        const asOneRecordLogs = itemLogger
            .asOneRecord()
            .info(`${failureMessage} ${heavyCrossMark}`, "red");
        if (cause !== undefined) {
            asOneRecordLogs.debug(`Cause: ${cause}`);
        }
        asOneRecordLogs.debug(
            `Total effective elapsed time: ${millisToString(result.elapsedTime.totalMillis)}`
        );
    }
}
