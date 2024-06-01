import {
    ConfigurationError,
    GenerationFailedError,
    LLMServiceError,
    RemoteConnectionError,
} from "../../../../llm/llmServiceErrors";
import {
    ErrorsHandlingMode,
    GeneratedProof,
    LLMService,
} from "../../../../llm/llmServices/llmService";
import { ModelParams } from "../../../../llm/llmServices/modelParams";
import {
    millisToString,
    timeToMillis,
    timeToString,
} from "../../../../llm/llmServices/utils/time";
import { ProofGenerationContext } from "../../../../llm/proofGenerationContext";

import {
    CompletionContext,
    SourceFileEnvironment,
    getTextBeforePosition,
    goalToTargetLemma,
    prepareProofToCheck,
} from "../../../../core/completionGenerator";
import { ContextTheoremsRanker } from "../../../../core/contextTheoremRanker/contextTheoremsRanker";
import {
    CoqLspTimeoutError,
    CoqProofChecker,
    ProofCheckResult,
} from "../../../../core/coqProofChecker";

import { Theorem } from "../../../../coqParser/parsedTypes";
import { stringifyAnyValue } from "../../../../utils/printers";
import { delay } from "../../../commonTestFunctions/delay";
import { BenchmarkingLogger } from "../logging/benchmarkingLogger";
import {
    BenchmarkedCompletionGeneration,
    CompletionGenerationFailureType,
    FailedCompletionGeneration,
    SuccessfulCompletionGeneration,
} from "../structures/benchmarkedItem";
import { BenchmarkingModelParams } from "../structures/benchmarkingModelParams";

import {
    CompletionGenerationTimeImpl,
    MeasuredProofImpl,
    TimeMark,
    measureElapsedMillis,
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
    coqProofChecker: CoqProofChecker,
    logger: BenchmarkingLogger
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
        .buildLogs()
        .append(`successfully generated ${generatedProofs.length} proofs`)
        .append(`elapsed time: ${proofsGenerationMillis} ms`, "gray")
        .info();
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

    const measuredProofCheckResultsOrFailure =
        await checkGeneratedProofsMeasured(
            preparedProofs,
            completionContext,
            sourceFileEnvironment,
            coqProofChecker,
            resultMetrics,
            logger
        );
    const proofsValidationFailure =
        measuredProofCheckResultsOrFailure as FailedCompletionGeneration;
    if (proofsValidationFailure !== null) {
        logger.info(
            `failed to validate proofs: ${proofsValidationFailure.causeMessage}`
        );
        return proofsValidationFailure;
    }

    const [proofCheckResults, proofsValidationMillis] =
        measuredProofCheckResultsOrFailure as [ProofCheckResult[], number];
    const validProofs = proofCheckResults
        .filter((checkResult) => checkResult.isValid)
        .map((checkResult) => new MeasuredProofImpl(checkResult.proof));
    measuredTime.addProofsValidationMillis(proofsValidationMillis);
    logger
        .buildLogs()
        .append(
            `successfully verified proofs: ${validProofs.length} / ${preparedProofs.length} are valid`
        )
        .append(`elapsed time: ${proofsValidationMillis} ms`, "gray")
        .info();

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
                .buildLogs()
                .append(
                    `attempt #${attemptIndex}, successfully generated proofs`
                )
                .append(
                    `total elapsed time (all ${attemptIndex + 1} attempts): ${millisToString(totalTime.measureElapsedMillis())}`
                )
                .debug();
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
                    `attempt #${attemptIndex}, configuration error: ${stringifyAnyValue(llmServiceError.message)}`
                );
                throw llmServiceError;
            }
            if (llmServiceError instanceof GenerationFailedError) {
                const estimatedTime =
                    llmService.estimateTimeToBecomeAvailable();
                delayMillis = timeToMillis(estimatedTime);
                logger
                    .buildLogs()
                    .append(
                        `attempt #${attemptIndex}, generation failed error: ${stringifyAnyValue(llmServiceError.message)}`
                    )
                    .append(
                        `estimated time to become available: ${timeToString(estimatedTime)}`
                    )
                    .debug();
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
                    .buildLogs()
                    .append(
                        `attempt #${attemptIndex}, remote connection error: ${stringifyAnyValue(llmServiceError.message)}`
                    )
                    .append(`delay to wait for: ${millisToString(delayMillis)}`)
                    .debug();
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

async function checkGeneratedProofsMeasured(
    preparedProofs: string[],
    completionContext: CompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    coqProofChecker: CoqProofChecker,
    resultMetrics: BenchmarkedCompletionGeneration,
    logger: BenchmarkingLogger
): Promise<[ProofCheckResult[], number] | FailedCompletionGeneration> {
    const sourceFileContentPrefix = getTextBeforePosition(
        sourceFileEnvironment.fileLines,
        completionContext.prefixEndPosition
    );
    try {
        return await measureElapsedMillis(async () => {
            return await coqProofChecker.checkProofs(
                sourceFileEnvironment.dirPath,
                sourceFileContentPrefix,
                completionContext.prefixEndPosition,
                preparedProofs
            );
        });
    } catch (e) {
        const error = e as Error;
        if (error === null) {
            throw Error(
                `got unexpected error from \`CoqProofChecker\`: ${stringifyAnyValue(e)}`
            );
        }
        if (error instanceof CoqLspTimeoutError) {
            logger.debug(
                `coq-lsp timeout error: ${stringifyAnyValue(error.message)}`
            );
            return buildFailedCompletionGeneration(
                resultMetrics,
                CompletionGenerationFailureType.TIMEOUT,
                error.message
            );
        } else {
            logger.debug(
                `\`CoqProofChecker\` error: ${stringifyAnyValue(error.message)}`
            );
            return buildFailedCompletionGeneration(
                resultMetrics,
                CompletionGenerationFailureType.COQ_PROOF_CHECKER_ERROR,
                error.message
            );
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
