import {
    ConfigurationError,
    GenerationFailedError,
    LLMServiceError,
    RemoteConnectionError,
} from "../../../llm/llmServiceErrors";
import { ErrorsHandlingMode } from "../../../llm/llmServices/commonStructures/errorsHandlingMode";
import { GeneratedRawContentItem } from "../../../llm/llmServices/commonStructures/generatedRawContent";
import { GenerationTokens } from "../../../llm/llmServices/commonStructures/generationTokens";
import { LLMServiceRequestSucceeded } from "../../../llm/llmServices/commonStructures/llmServiceRequest";
import {
    LLMService,
    LLMServiceImpl,
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
} from "../../../core/completionGenerationContext";
import { ContextTheoremsRanker } from "../../../core/contextTheoremRanker/contextTheoremsRanker";
import { prepareProofToCheck } from "../../../core/exposedCompletionGeneratorUtils";
import { goalToTargetLemma } from "../../../core/exposedCompletionGeneratorUtils";

import { Theorem } from "../../../coqParser/parsedTypes";
import { EventLogger } from "../../../logging/eventLogger";
import { delay } from "../../../test/commonTestFunctions/delay";
import { stringifyAnyValue } from "../../../utils/printers";
import { BenchmarkingLogger } from "../logging/benchmarkingLogger";
import { BenchmarkingModelParams } from "../structures/benchmarkingCore/benchmarkingModelParams";
import {
    BenchmarkedCompletionGeneration,
    CompletionGenerationFailureType,
    FailedCompletionGeneration,
    SuccessfulCompletionGeneration,
} from "../structures/benchmarkingResults/benchmarkedItem";
import { WorkspaceRoot } from "../structures/common/workspaceRoot";
import { ParsedCoqFileData } from "../structures/parsedCoqFile/parsedCoqFileData";
import { AsyncScheduler } from "../utils/asyncScheduler";
import { reduceToMap } from "../utils/mapUtils";
import { hasAllPropertiesDefined } from "../utils/structsUtils";

import {
    CompletionGenerationTimeImpl,
    MeasuredProofImpl,
    TimeMark,
} from "./measureUtils";
import {
    AbstractProofsChecker,
    ProofsCheckFailedError,
    ProofsCheckResult,
} from "./proofsCheckers/abstractProofsChecker";

export interface CompletionGenerationBenchmarkArgs<
    ResolvedModelParams extends ModelParams,
    LLMServiceType extends LLMService<any, ResolvedModelParams>,
> {
    completionContext: CompletionContext;
    sourceFileEnvironment: SourceFileEnvironment;
    benchmarkingModelParams: BenchmarkingModelParams<ResolvedModelParams>;
    llmService: LLMServiceType;
    llmServiceEventLogger: EventLogger;
    parsedSourceFileData: ParsedCoqFileData;
    workspaceRoot: WorkspaceRoot;
}

/**
 * Executes a single completion generation and measures its associated metrics.
 * Note: this function does not support multi-round generation so far (TODO).
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
    generationArgs: CompletionGenerationBenchmarkArgs<
        ResolvedModelParams,
        LLMServiceType
    >,
    modelsScheduler: AsyncScheduler,
    logger: BenchmarkingLogger,
    proofsChecker: AbstractProofsChecker
): Promise<BenchmarkedCompletionGeneration> {
    const proofGenerationResult = await generateProofWithRetriesExclusively(
        generationArgs,
        modelsScheduler,
        logger
    );
    logger
        .asOneRecord()
        .info(
            `Successfully generated ${proofGenerationResult.generatedRawProofs.length} proofs`
        )
        .debug(
            `Effective elapsed time: ${proofGenerationResult.effectiveElapsedTimeMillis} ms`,
            "gray"
        );
    const preparedProofsWithTokens: [string, GenerationTokens][] =
        proofGenerationResult.generatedRawProofs.map(
            (generatedRawProof: GeneratedRawContentItem) => [
                prepareProofToCheck(generatedRawProof.content),
                generatedRawProof.tokensSpent,
            ]
        );

    const measuredTime = new CompletionGenerationTimeImpl(
        proofGenerationResult.effectiveElapsedTimeMillis
    );
    const allGeneratedProofsMap = reduceToMap(
        preparedProofsWithTokens,
        ([proof, _]) => proof,
        ([proof, tokens]) => new MeasuredProofImpl(proof, tokens)
    );

    const parsedSourceFile = generationArgs.parsedSourceFileData;
    let resultMetrics: BenchmarkedCompletionGeneration = {
        allGeneratedProofs: Array.from(allGeneratedProofsMap.values()),
        contextTheorems: proofGenerationResult.contextTheoremNames.map(
            (theoremName) => {
                const theorem =
                    parsedSourceFile.theoremsByNames.get(theoremName);
                if (theorem === undefined) {
                    throw Error(
                        `Proof generation invariant failed: a context theorem with the name "${theoremName}" was not found in the parsed data of the file ${parsedSourceFile.filePath}`
                    );
                }
                return theorem;
            }
        ),
        tokensSpentInTotal: proofGenerationResult.tokensSpentInTotal,
        elapsedTime: measuredTime,
    };

    let proofsCheckResult: ProofsCheckResult;
    try {
        proofsCheckResult = await proofsChecker.checkProofs(
            preparedProofsWithTokens.map(([proof, _]) => proof),
            generationArgs.completionContext,
            generationArgs.sourceFileEnvironment,
            generationArgs.workspaceRoot,
            logger
        );
    } catch (error) {
        if (error instanceof ProofsCheckFailedError) {
            logger.info(`Failed to validate proofs: ${error.causeMessage}`);
            return buildFailedCompletionGeneration(
                resultMetrics,
                CompletionGenerationFailureType[error.failureType],
                error.causeMessage
            );
        } else {
            throw error;
        }
    }
    const validProofs = proofsCheckResult.checkedProofs
        .filter((checkedProof) => checkedProof.isValid)
        .map((checkedProof) => allGeneratedProofsMap.get(checkedProof.proof)!);
    measuredTime.addProofsValidationMillis(
        proofsCheckResult.effectiveElapsedMillis
    );
    logger
        .asOneRecord()
        .info(
            `Successfully verified proofs: ${validProofs.length} / ${preparedProofsWithTokens.length} are valid`
        )
        .debug(
            `Effective elapsed time: ${proofsCheckResult.effectiveElapsedMillis} ms`,
            "gray"
        );

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

interface ProofGenerationResult {
    generatedRawProofs: GeneratedRawContentItem[];
    tokensSpentInTotal: GenerationTokens;
    contextTheoremNames: string[];
    effectiveElapsedTimeMillis: number;
}

/**
 * Note: scheduling could be done (in other words, "the same model semaphore" could be captured)
 * more granurarly: namely, for each generation request and not for a whole `while` proof-generation cycle with retries.
 * Such scheduling might improve performance indeed;
 * however, this improvement could be possible only if the retries algorithm is not optimal enough
 * (i.e. if the running task waits for too long despite the fact that the service is already available).
 * Thus, a more reliable approach has been chosen so far: to wait until the running task suceeds with its retries and gets the response.
 * This way, it is guaranteed that the system proceeds in general: requests are not too frequent to fail the remote service.
 */
async function generateProofWithRetriesExclusively<
    ResolvedModelParams extends ModelParams,
>(
    generationArgs: CompletionGenerationBenchmarkArgs<ResolvedModelParams, any>,
    modelsScheduler: AsyncScheduler,
    logger: BenchmarkingLogger
): Promise<ProofGenerationResult> {
    return modelsScheduler.scheduleTask(
        () =>
            generateProofWithRetriesMeasured(
                generationArgs.completionContext,
                generationArgs.sourceFileEnvironment,
                generationArgs.benchmarkingModelParams,
                generationArgs.llmService,
                generationArgs.llmServiceEventLogger,
                logger
            ),
        logger
    );
}

async function generateProofWithRetriesMeasured<
    ResolvedModelParams extends ModelParams,
>(
    completionContext: CompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    benchmarkingModelParams: BenchmarkingModelParams<ResolvedModelParams>,
    llmService: LLMService<any, any>,
    llmServiceEventLogger: EventLogger,
    logger: BenchmarkingLogger
): Promise<ProofGenerationResult> {
    const result: Partial<ProofGenerationResult> = {};
    const succeededSubscriptionId = llmServiceEventLogger.subscribeToLogicEvent(
        LLMServiceImpl.requestSucceededEvent,
        (data: any) => {
            const request = data as LLMServiceRequestSucceeded;
            if (request === null) {
                throw Error(
                    `data of the ${LLMServiceImpl.requestSucceededEvent} event should be a \`LLMServiceRequestSucceeded\` object, but data = ${stringifyAnyValue(data)}`
                );
            }
            result.generatedRawProofs = request.generatedRawProofs;
            result.tokensSpentInTotal = request.tokensSpentInTotal;
            result.contextTheoremNames =
                request.analyzedChat?.contextTheorems ?? [];
        }
    );

    const proofGenerationContext = buildProofGenerationContext(
        completionContext,
        sourceFileEnvironment.fileTheorems,
        benchmarkingModelParams.theoremRanker
    );

    let delayMillis = 0;
    let prevFailureIsConnectionError = false;
    let attemptIndex = 0;

    let totalTime = new TimeMark();
    while (true) {
        try {
            const attemptTime = new TimeMark();
            await llmService.generateProof(
                proofGenerationContext,
                benchmarkingModelParams.modelParams,
                benchmarkingModelParams.modelParams.defaultChoices,
                ErrorsHandlingMode.RETHROW_ERRORS
            );
            result.effectiveElapsedTimeMillis =
                attemptTime.measureElapsedMillis();
            if (!hasAllPropertiesDefined<ProofGenerationResult>(result)) {
                throw Error(
                    "Proof generation invariant failed: proofs were generated, but a request-succeeded event was not sent"
                );
            }

            logger
                .asOneRecord()
                .debug(
                    `Attempt #${attemptIndex}, successfully generated proofs`
                )
                .debug(
                    `Total elapsed time (all ${attemptIndex + 1} attempts): ${millisToString(totalTime.measureElapsedMillis())}`
                );
            llmServiceEventLogger.unsubscribe(
                LLMServiceImpl.requestSucceededEvent,
                succeededSubscriptionId
            );

            return result;
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
