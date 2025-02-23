import { ErrorsHandlingMode } from "../../../llm/llmServices/commonStructures/errorsHandlingMode";
import { LLMService } from "../../../llm/llmServices/llmService";
import { ModelParams } from "../../../llm/llmServices/modelParams";

import { IllegalStateError, unreachable } from "../../../utils/throwErrors";
import { BenchmarkingLogger } from "../logging/benchmarkingLogger";
import { BenchmarkingItem } from "../structures/benchmarkingCore/benchmarkingItem";
import { BenchmarkingOptions } from "../structures/benchmarkingCore/benchmarkingOptions";
import {
    BenchmarkedItem,
    BenchmarkingResult,
} from "../structures/benchmarkingResults/benchmarkedItem";
import { throwOnAbort } from "../utils/asyncUtils/abortUtils";
import { AsyncScheduler } from "../utils/asyncUtils/asyncScheduler";
import { selectLLMServiceBuilder } from "../utils/commonStructuresUtils/llmServicesUtils";
import { joinPaths, provideEmptyDirectoryOrThrow } from "../utils/fileUtils/fs";
import { benchmarkingInvariantFailed } from "../utils/throwErrors";

import { ExecuteBenchmarkingTaskErrorHandlingUtils } from "./executeBenchmarkingTaskUtils/errorHandling";
import { ExecuteBenchmarkingTaskLoggingUtils } from "./executeBenchmarkingTaskUtils/logging";
import { ExecuteBenchmarkingTaskArtifactsUtils } from "./executeBenchmarkingTaskUtils/saveArtifacts";
import {
    CompletionGenerationBenchmarkArgs,
    ParentProofToFix,
    benchmarkSingleCompletionGeneration,
} from "./singleCompletionGeneration/benchmarkSingleCompletionGeneration";
import { AbstractProofsChecker } from "./singleCompletionGeneration/proofsCheckers/abstractProofsChecker";

import ArtifactsUtils = ExecuteBenchmarkingTaskArtifactsUtils;
import ErrorHandling = ExecuteBenchmarkingTaskErrorHandlingUtils;
import Logging = ExecuteBenchmarkingTaskLoggingUtils;

namespace ArtifactsNames {
    export const benchmarkingItemFileName = "input-task.json";
    export const resultReportFileName = "result.json";
}

/**
 * Executes the full benchmarking process for a given completion generation benchmarking task.
 *
 * Specifically, this function sequentially benchmarks individual rounds of completion generation
 * by invoking `benchmarkSingleCompletionGeneration`. The rounds follow a BFS order:
 * - Initially, the root round of proof generation is benchmarked.
 * - Next, proof fixes for any non-valid generated proofs are benchmarked in the second round.
 * - Subsequent rounds benchmark proof fixes for non-valid proofs from the previous round, continuing this process iteratively.
 *
 * The multiround benchmarking mirrors the original multiround completion generation process:
 * execution stops as soon as any valid proof is generated.
 *
 * Additionally, this function saves interim and final benchmarking results to `saveToDirPath`
 * to ensure no generated data is lost in case of failure, allowing the benchmarking task
 * to be resumed in the future if needed.
 *
 * Generally, this function does not throw errors; however, if `failFast` is enabled,
 * all errors are rethrown to cancel promises and halt execution.
 * Any encountered errors are logged appropriately in any case.
 * - Errors encountered during proof generation are captured within the `BenchmarkedItem` by
 *   `benchmarkSingleCompletionGeneration` (refer to its documentation for details). However,
 *   such errors terminate the multiround benchmarking process. For further explanation, see
 *   the comment at the `if (childRoundResult.isFailedToFinishRound())` line in the code below.
 * - Other expected errors, such as `BenchmarkingError` or `ConfigurationError`, also interrupt
 *   the benchmarking process, resulting in the function returning `undefined`.
 * - Finally, `IllegalStateError` is always rethrown, as it indicates internal invariant violations
 *   that could lead to unpredictable behavior.
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
    provideEmptyDirectoryOrThrow(
        saveToDirPath,
        "item artifacts",
        (errorMessage) =>
            benchmarkingInvariantFailed(
                itemLogger,
                `${saveToDirPath} was expected to be provided initially empty, `,
                `but: ${errorMessage}`
            )
    );
    const task = benchmarkingItem.task;
    const params = benchmarkingItem.params;

    const llmService = selectLLMServiceBuilder(
        benchmarkingItem.params.llmServiceIdentifier
    )(undefined, ErrorsHandlingMode.RETHROW_ERRORS);

    try {
        ArtifactsUtils.saveInputTaskToFileOrThrow(
            benchmarkingItem,
            joinPaths(saveToDirPath, ArtifactsNames.benchmarkingItemFileName)
        );

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
            const parentProofDesc =
                parentProof === undefined
                    ? "generate proofs"
                    : `proof to fix id: ${parentProof?.benchmarkedProof.generatedProofId}`;
            const thisRoundLogger = itemLogger.createChildLoggerWithIdentifier(
                `[round: ${roundNumber}, ${parentProofDesc}]`
            );
            const result = await benchmarkSingleCompletionGeneration(
                thisRoundGenerationArgs,
                options,
                modelsScheduler,
                thisRoundLogger,
                proofsChecker,
                abortSignal
            );
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
                    rootResult = childRoundResult;
                } else {
                    // link target proof and the result of its proof-fix generation
                    parentProof.benchmarkedProof.linkNextRoundResult(
                        childRoundResult
                    );
                    childRoundResult.linkParentProofToFix(
                        parentProof.benchmarkedProof
                    );
                }

                Logging.logRoundResult(childRoundResult, itemLogger);
                ArtifactsUtils.saveRoundResultToFileOrThrow(
                    childRoundResult,
                    joinPaths(
                        saveToDirPath,
                        ArtifactsUtils.buildRoundResultFileName(
                            roundNumber,
                            parentProof?.benchmarkedProof.generatedProofId
                        )
                    )
                );

                if (
                    childRoundResult.isFailedToFinishRound() ||
                    childRoundResult.isSuccessfulCompletion()
                ) {
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
        Logging.logFinalResult(benchmarkedItem.result, itemLogger);
        ArtifactsUtils.saveResultToFile(
            benchmarkedItem.result,
            joinPaths(saveToDirPath, ArtifactsNames.resultReportFileName),
            itemLogger
        );

        return benchmarkedItem;
    } catch (e) {
        const wrappedError = ErrorHandling.wrapUnexpectedErrorAsIllegalState(e);
        ErrorHandling.logErrorIfNeeded(
            wrappedError,
            itemLogger,
            params,
            options,
            abortSignal
        );
        if (options.failFast || wrappedError instanceof IllegalStateError) {
            throw wrappedError;
        }
        return undefined;
    } finally {
        llmService.dispose();
    }
}
