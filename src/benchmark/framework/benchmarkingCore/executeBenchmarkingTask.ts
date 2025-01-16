import { ConfigurationError } from "../../../llm/llmServiceErrors";
import { ErrorsHandlingMode } from "../../../llm/llmServices/commonStructures/errorsHandlingMode";
import { LLMService } from "../../../llm/llmServices/llmService";
import { ModelParams } from "../../../llm/llmServices/modelParams";

import { buildErrorCompleteLog } from "../../../utils/errorsUtils";
import { toFormattedJsonString } from "../../../utils/printers";
import { illegalState, unreachable } from "../../../utils/throwErrors";
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
import { benchmarkingInvariantFailed } from "../utils/throwErrors";

import {
    CompletionGenerationBenchmarkArgs,
    ParentProofToFix,
    benchmarkSingleCompletionGeneration,
} from "./singleCompletionGeneration/benchmarkSingleCompletionGeneration";
import { AbstractProofsChecker } from "./singleCompletionGeneration/proofsCheckers/abstractProofsChecker";

namespace ArtifactsNames {
    export const benchmarkingItemFileName = "input-task.json";
    export const resultReportFileName = "result.json";
}

/**
 * Executes the full benchmarking process for a given completion generation benchmarking task.
 *
 * Specifically, this function calls `benchmarkSingleCompletionGeneration` to benchmark individual
 * rounds of completion generation. Benchmarking rounds are executed sequentially in BFS order:
 * - First, the root round of proof generation is benchmarked.
 * - Then, proof fixes for any resulting non-valid generated proofs are benchmarked in the second round.
 * - Subsequently, proof fixes for non-valid proofs from the second round are benchmarked in the third round, and so on.
 *
 * The multiround benchmarking mirrors the original multiround completion generation process:
 * execution stops as soon as any valid proof is generated.
 *
 * Additionally, this function saves interim and final benchmarking results to `saveToDirPath`
 * to ensure no generated data is lost in case of failure, allowing the benchmarking task
 * to be resumed in the future if needed.
 *
 * This function generally does not throw errors, except for `FailFastAbortError`, which
 * enforces a fail-fast abort strategy. Errors anticipated during proof generation are captured
 * in the `BenchmarkedItem` by `benchmarkSingleCompletionGeneration` (refer to its documentation
 * for more details). However, these errors also stop the multiround benchmarking process.
 * For further explanation, see the comment at the `if (childRoundResult.isFailedToFinishRound())`
 * line in the code below.
 *
 * Other errors (e.g., `ConfigurationError`, `IllegalStateError`) will interrupt the
 * benchmarking process. They are logged appropriately, and the function returns `undefined`.
 */
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

    const llmService = selectLLMServiceBuilder(
        benchmarkingItem.params.llmServiceIdentifier
    )(undefined, ErrorsHandlingMode.RETHROW_ERRORS);

    const logError = (e: any) =>
        logCommonError(e, itemLogger, params, options, abortSignal);

    try {
        const generationArgs: CompletionGenerationBenchmarkArgs<
            ModelParams,
            LLMService<any, ModelParams>
        > = {
            completionContext: task.getCompletionContext(),
            sourceTheorem: task.sourceTheorem,
            sourceFileEnvironment: task.getSourceFileEnvironment(),
            benchmarkingModelParams: params,
            parentProofToFix: undefined,
            nextGeneratedProofId: 0,
            roundNumber: 1,
            llmService: llmService,
            parsedSourceFileData: task.parsedSourceFileData,
            workspaceRoot: task.workspaceRoot,
        };

        async function benchmarkCompletionGenerationRound(
            parentProof: ParentProofToFix | undefined,
            nextGeneratedProofId: number,
            roundNumber: number
        ): Promise<BenchmarkingResult> {
            const thisRoundGenerationArgs = {
                ...generationArgs,
                parentProofToFix: parentProof,
                nextGeneratedProofId: nextGeneratedProofId,
                roundNumber: roundNumber,
            };
            const result = await benchmarkSingleCompletionGeneration(
                thisRoundGenerationArgs,
                options,
                modelsScheduler,
                itemLogger,
                proofsChecker,
                abortSignal
            );
            logRoundResult(result, itemLogger);
            return result;
        }

        let rootResult: BenchmarkingResult | undefined = undefined;

        const maxRoundsNumber =
            params.modelParams.multiroundProfile.maxRoundsNumber;
        let curRoundProofsToFix: (ParentProofToFix | undefined)[] = [undefined];
        let nextGeneratedProofId = 0;

        for (
            let roundNumber = 1;
            roundNumber <= maxRoundsNumber;
            roundNumber++
        ) {
            throwOnAbort(abortSignal);
            const nextRoundProofsToFix: ParentProofToFix[] = [];
            for (const parentProof of curRoundProofsToFix) {
                const childRoundResult =
                    await benchmarkCompletionGenerationRound(
                        parentProof,
                        nextGeneratedProofId,
                        roundNumber
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
                            roundNumber,
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
            result:
                rootResult ??
                unreachable(
                    "either root round throws or its result is saved in `rootResult`"
                ),
        };
        logFinalResult(benchmarkedItem.result, itemLogger);
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
    roundNumber: number,
    parentProofToFixId: number | undefined
): string {
    const parentId =
        parentProofToFixId === undefined
            ? `generate-proofs`
            : `fix-proof-${parentProofToFixId}`;
    return buildSafeJsonFileName(`round-${roundNumber}-${parentId}`);
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

function logRoundResult(
    roundResult: BenchmarkingResult,
    itemLogger: BenchmarkingLogger
) {
    const roundId =
        roundResult.parentProofToFixId === undefined
            ? "Root round of proof generation"
            : `Round ${roundResult.roundNumber} of fixing proof ${roundResult.parentProofToFixId}`;
    const asOneRecordLogs = itemLogger.asOneRecord();
    const logElapsedTime = () =>
        asOneRecordLogs.debug(
            `This round effective elapsed time: ${millisToString(roundResult.roundElapsedTime.totalMillis)}`
        );

    if (roundResult.isSuccessfullyFinishedRound()) {
        asOneRecordLogs.info(`${roundId} has been successfully finished:`);
        if (roundResult.isSuccessfulCompletion()) {
            asOneRecordLogs
                .info(`Valid proof has been found ${heavyCheckMark}`)
                .debug("First valid proof:")
                .debug(roundResult.thisRoundValidProofs[0].asString);
        } else {
            asOneRecordLogs.debug(
                `However, no valid proofs have been found ${heavyCrossMark}`
            );
        }
        const generatedProofsIds = roundResult.generatedProofs
            .map((proof) => `${proof.generatedProofId}`)
            .join(", ");
        asOneRecordLogs.debug(
            `Newly generated proofs id-s are: [${generatedProofsIds}]`
        );
        logElapsedTime();
    } else {
        const { failureType, causeMessage } = roundResult.failureMetadata;
        asOneRecordLogs
            .error(`${roundId} has failed to finish: ${failureType}`, "default")
            .error(`Cause: ${causeMessage}`, "default");
        logElapsedTime();
        asOneRecordLogs.error(
            "This benchmarking task execution will be stopped"
        );
    }
}

function logFinalResult(
    finalResult: BenchmarkingResult,
    itemLogger: BenchmarkingLogger
) {
    const asOneRecordLogs = itemLogger.asOneRecord();
    if (finalResult.isSuccessfulCompletion()) {
        const firstValidProof = finalResult.getAllValidProofs()[0];
        asOneRecordLogs
            .info(`Goal was succefully proven ${heavyCheckMark}`, "green")
            .debug(
                `First valid proof was generated at round ${firstValidProof.proofObject.versionNumber}:`
            )
            .debug(`${firstValidProof.asString}`);
    } else {
        let logFailure: (message: string) => void;
        let failureMessage: string;
        let cause: string | undefined = undefined;
        if (finalResult.hasSuccessfullyFinished()) {
            logFailure = (message) => asOneRecordLogs.info(message, "red");
            failureMessage = "Valid proofs not found";
        } else {
            logFailure = (message) => asOneRecordLogs.error(message);

            const allFailedRounds = finalResult.getAllFailedToFinishRounds();
            if (allFailedRounds.length > 1) {
                benchmarkingInvariantFailed(
                    itemLogger,
                    "there are more than one failed rounds ",
                    "in the final benchmarking result mutliround tree; ",
                    "according to the implemented policy, the multiround benchmarking ",
                    "should be stopped as soon as the first failure occurred\nFailed nodes:\n",
                    allFailedRounds
                        .map((failedRound) =>
                            [
                                `{ roundNumber: ${failedRound.roundNumber}; `,
                                `parentProofToFixId: ${failedRound.parentProofToFixId}; `,
                                `cause: ${failedRound.failureMetadata.failureType}, ${failedRound.failureMetadata.causeMessage} }`,
                            ].join("")
                        )
                        .join(",\n")
                );
            }
            if (allFailedRounds.length === 0) {
                illegalState(
                    "`finalResult.hasSuccessfullyFinished()` returned false,",
                    "but there are no failed rounds in its multiround subtree"
                );
            }
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

        logFailure(`${failureMessage} ${heavyCrossMark}`);
        if (cause !== undefined) {
            asOneRecordLogs.debug(`Cause: ${cause}`);
        }
    }

    asOneRecordLogs.debug(
        `Total effective elapsed time: ${millisToString(finalResult.getTotalElapsedTime().totalMillis)}`
    );
}
