import {
    ConfigurationError,
    GenerationFailedError,
    LLMServiceError,
    RemoteConnectionError,
} from "../../../llm/llmServiceErrors";
import {
    ErrorsHandlingMode,
    GeneratedProof,
    LLMService,
} from "../../../llm/llmServices/llmService";
import { ModelParams } from "../../../llm/llmServices/modelParams";
import {
    millisToString,
    timeToMillis,
    timeToString,
} from "../../../llm/llmServices/utils/time";
import { ProofGenerationContext } from "../../../llm/proofGenerationContext";

import {
    CompletionContext,
    SourceFileEnvironment,
    goalToTargetLemma,
    prepareProofToCheck,
} from "../../../core/completionGenerator";
import { ContextTheoremsRanker } from "../../../core/contextTheoremRanker/contextTheoremsRanker";

import { Theorem } from "../../../coqParser/parsedTypes";
import { delay } from "../../../test/commonTestFunctions/delay";
import { stringifyAnyValue } from "../../../utils/printers";
import { BenchmarkingLogger } from "../logging/benchmarkingLogger";
import {
    BenchmarkedCompletionGeneration,
    CompletionGenerationFailureType,
    FailedCompletionGeneration,
    SuccessfulCompletionGeneration,
} from "../structures/benchmarkedItem";
import { BenchmarkingModelParams } from "../structures/benchmarkingModelParams";
import { WorkspaceRoot } from "../structures/completionGenerationTask";
import { ExperimentRunOptions } from "../structures/experimentRunOptions";
import { checkGeneratedProofsInSubprocess } from "../subprocessCalls/checkGeneratedProofs/callChildProcess";
import { CheckProofsBySubprocessSignature } from "../subprocessCalls/checkGeneratedProofs/callSignature";
import { AsyncScheduler } from "../utils/asyncScheduler";

import {
    CompletionGenerationTimeImpl,
    MeasuredProofImpl,
    TimeMark,
} from "./measureUtils";

/**
 * Executes a single completion generation and measures its associated metrics.
 * Note: this function does not support multi-round generation.
 *
 * If proof generation fails due to the `llmService` being unavailable or unreachable (e.g., connection error),
 * the function will retry indefinitely. The retries will occur with delays as specified in
 * `LLMService.estimateTimeToBecomeAvailable` and `RemoteConnectionErrorDelays`, until a response with proofs is received.
 *
 * Typically, this function does not throw errors:
 * expected errors are encapsulated within `FailedCompletionGeneration`.
 * However, the following exceptions will be handled differently:
 * - `ConfigurationError`-s will always be rethrown;
 * - errors will be thrown if internal invariants are violated.
 */
export async function benchmarkSingleCompletionGeneration<
    ResolvedModelParams extends ModelParams,
    LLMServiceType extends LLMService<any, ResolvedModelParams>,
>(
    completionContext: CompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    benchmarkingModelParams: BenchmarkingModelParams<ResolvedModelParams>,
    llmService: LLMServiceType,
    workspaceRoot: WorkspaceRoot,
    logger: BenchmarkingLogger,
    subprocessesScheduler: AsyncScheduler,
    experimentRunOptions: ExperimentRunOptions
): Promise<BenchmarkedCompletionGeneration> {
    const [generatedProofs, proofsGenerationMillis] =
        await generateProofWithRetriesMeasured(
            completionContext,
            sourceFileEnvironment,
            benchmarkingModelParams,
            llmService,
            logger
        );
    logger
        .asOneRecord()
        .info(`Successfully generated ${generatedProofs.length} proofs`)
        .debug(`Elapsed time: ${proofsGenerationMillis} ms`, "gray");
    const preparedProofs = generatedProofs.map(
        (generatedProof: GeneratedProof) =>
            prepareProofToCheck(generatedProof.proof())
    );
    const measuredTime = new CompletionGenerationTimeImpl(
        proofsGenerationMillis
    );

    let resultMetrics: BenchmarkedCompletionGeneration = {
        allGeneratedProofs: preparedProofs.map(
            (proof) => new MeasuredProofImpl(proof)
        ),
        elapsedTime: measuredTime,
        contextTheorems: undefined, // TODO
        chatTokens: undefined, // TODO
    };

    const proofsValidationExecutionResult =
        await checkGeneratedProofsInSubprocess(
            preparedProofs,
            completionContext,
            sourceFileEnvironment,
            workspaceRoot,
            experimentRunOptions.checkProofsSubprocessTimeoutMillis,
            subprocessesScheduler,
            logger,
            experimentRunOptions.enableSubprocessLifetimeDebugLogs
        );
    if (proofsValidationExecutionResult.isFailed()) {
        // proofs check throws only `Error`-s
        throw Error(proofsValidationExecutionResult.errorMessage);
    }
    const proofsValidationResult = proofsValidationExecutionResult.maybeResult!;
    if (CheckProofsBySubprocessSignature.isFailure(proofsValidationResult)) {
        const failureCauseMessage = proofsValidationResult.causeMessage;
        logger.info(`Failed to validate proofs: ${failureCauseMessage}`);
        return buildFailedCompletionGeneration(
            resultMetrics,
            CompletionGenerationFailureType[proofsValidationResult.failureType],
            failureCauseMessage
        );
    }

    const { proofCheckResults, proofsValidationMillis } =
        proofsValidationResult as CheckProofsBySubprocessSignature.SuccessResult;
    const validProofs = proofCheckResults
        .filter((checkResult) => checkResult.isValid)
        .map((checkResult) => new MeasuredProofImpl(checkResult.proof));
    measuredTime.addProofsValidationMillis(proofsValidationMillis);
    logger
        .asOneRecord()
        .info(
            `Successfully verified proofs: ${validProofs.length} / ${preparedProofs.length} are valid`
        )
        .debug(`Elapsed time: ${proofsValidationMillis} ms`, "gray");

    if (validProofs.length > 0) {
        const successfulGeneration: SuccessfulCompletionGeneration = {
            ...resultMetrics,
            validProofs: validProofs,
        };
        return successfulGeneration;
    } else {
        return buildFailedCompletionGeneration(
            resultMetrics,
            CompletionGenerationFailureType.SEARCH_FAILED,
            "No valid completions found"
        );
    }
}

namespace RemoteConnectionErrorDelays {
    export const initialDelayMillis = 10_000;
    export const exponentialMultiplier = 2;
}

async function generateProofWithRetriesMeasured<
    ResolvedModelParams extends ModelParams,
>(
    completionContext: CompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    benchmarkingModelParams: BenchmarkingModelParams<ResolvedModelParams>,
    llmService: LLMService<any, any>,
    logger: BenchmarkingLogger
): Promise<[GeneratedProof[], number]> {
    let delayMillis = 0;
    let prevFailureIsConnectionError = false;
    let attemptIndex = 0;
    let totalTime = new TimeMark();
    while (true) {
        try {
            const attemptTime = new TimeMark();
            const generatedProofs = await llmService.generateProof(
                buildProofGenerationContext(
                    completionContext,
                    sourceFileEnvironment.fileTheorems,
                    benchmarkingModelParams.theoremRanker
                ),
                benchmarkingModelParams.modelParams,
                benchmarkingModelParams.modelParams.defaultChoices,
                ErrorsHandlingMode.RETHROW_ERRORS
            );
            const measuredTime = attemptTime.measureElapsedMillis();
            logger
                .asOneRecord()
                .debug(
                    `Attempt #${attemptIndex}, successfully generated proofs`
                )
                .debug(
                    `Total elapsed time (all ${attemptIndex + 1} attempts): ${millisToString(totalTime.measureElapsedMillis())}`
                );
            return [generatedProofs, measuredTime];
        } catch (e) {
            const llmServiceError = e as LLMServiceError;
            if (llmServiceError === null) {
                throw Error(
                    `LLMService is expected to throw only \`LLMServiceError\`-s, but got: ${stringifyAnyValue(e)}`
                );
            }
            if (llmServiceError instanceof ConfigurationError) {
                logger.debug(
                    `Attempt #${attemptIndex}, configuration error: ${stringifyAnyValue(llmServiceError.message)}`
                );
                throw llmServiceError;
            }
            if (llmServiceError instanceof GenerationFailedError) {
                const estimatedTime =
                    llmService.estimateTimeToBecomeAvailable();
                delayMillis = timeToMillis(estimatedTime);
                logger
                    .asOneRecord()
                    .debug(
                        `Attempt #${attemptIndex}, generation failed error: ${stringifyAnyValue(llmServiceError.message)}`
                    )
                    .debug(
                        `Estimated time to become available: ${timeToString(estimatedTime)}`
                    );
            } else if (llmServiceError instanceof RemoteConnectionError) {
                if (prevFailureIsConnectionError) {
                    delayMillis *=
                        RemoteConnectionErrorDelays.exponentialMultiplier;
                } else {
                    delayMillis =
                        RemoteConnectionErrorDelays.initialDelayMillis;
                    prevFailureIsConnectionError = true;
                }
                logger
                    .asOneRecord()
                    .debug(
                        `Attempt #${attemptIndex}, remote connection error: ${stringifyAnyValue(llmServiceError.message)}`
                    )
                    .debug(`Delay to wait for: ${millisToString(delayMillis)}`);
            } else {
                throw Error(
                    `unknown \`LLMServiceError\` type: ${stringifyAnyValue(llmServiceError.name)}, ${stringifyAnyValue(llmServiceError)}`
                );
            }
            // wait and try again
            await delay(delayMillis);
            attemptIndex += 1;
        }
    }
}

function buildProofGenerationContext(
    completionContext: CompletionContext,
    fileTheorems: Theorem[],
    theoremRanker?: ContextTheoremsRanker
): ProofGenerationContext {
    const rankedTheorems =
        theoremRanker?.rankContextTheorems(fileTheorems, completionContext) ??
        fileTheorems;
    return {
        contextTheorems: rankedTheorems,
        completionTarget: goalToTargetLemma(completionContext.proofGoal),
    };
}

function buildFailedCompletionGeneration(
    resultMetrics: BenchmarkedCompletionGeneration,
    failureType: CompletionGenerationFailureType,
    causeMessage: string
): FailedCompletionGeneration {
    const failedGeneration: FailedCompletionGeneration = {
        ...resultMetrics,
        failureType: failureType,
        causeMessage: causeMessage,
    };
    return failedGeneration;
}
