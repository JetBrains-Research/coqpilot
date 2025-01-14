import {
    ConfigurationError,
    GenerationFailedError,
    LLMServiceError,
    RemoteConnectionError,
} from "../../../../llm/llmServiceErrors";
import { ErrorsHandlingMode } from "../../../../llm/llmServices/commonStructures/errorsHandlingMode";
import { GeneratedRawContentItem } from "../../../../llm/llmServices/commonStructures/generatedRawContent";
import { GenerationTokens } from "../../../../llm/llmServices/commonStructures/generationTokens";
import { LLMServiceRequestSucceeded } from "../../../../llm/llmServices/commonStructures/llmServiceRequest";
import {
    GeneratedProof,
    GeneratedProofImpl,
} from "../../../../llm/llmServices/generatedProof";
import {
    LLMService,
    LLMServiceImpl,
} from "../../../../llm/llmServices/llmService";
import { ModelParams } from "../../../../llm/llmServices/modelParams";
import { ProofGenerationContext } from "../../../../llm/proofGenerationContext";

import {
    CompletionContext,
    SourceFileEnvironment,
} from "../../../../core/completionGenerationContext";
import { ContextTheoremsRanker } from "../../../../core/contextTheoremRanker/contextTheoremsRanker";
import { prepareProofToCheck } from "../../../../core/exposedCompletionGeneratorUtils";
import { goalToTargetLemma } from "../../../../core/exposedCompletionGeneratorUtils";

import { Theorem } from "../../../../coqParser/parsedTypes";
import { EventLogger } from "../../../../logging/eventLogger";
import { delay } from "../../../../utils/delay";
import { buildErrorCompleteLog } from "../../../../utils/errorsUtils";
import { stringifyAnyValue } from "../../../../utils/printers";
import { illegalState, invariantFailed } from "../../../../utils/throwErrors";
import {
    millisToString,
    timeToMillis,
    timeToString,
} from "../../../../utils/time";
import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { writeTeamCityStatisticsValue } from "../../logging/consoleWriteUtils";
import { BenchmarkingModelParams } from "../../structures/benchmarkingCore/benchmarkingModelParams";
import { BenchmarkingOptions } from "../../structures/benchmarkingCore/benchmarkingOptions";
import {
    BenchmarkingResult,
    FailedCompletionGenerationBenchmarking,
    SuccessfulCompletionGenerationBenchmarking,
} from "../../structures/benchmarkingResults/benchmarkedItem";
import {
    NonValidatedProof,
    ValidatedProof,
} from "../../structures/benchmarkingResults/benchmarkedProof";
import { WorkspaceRoot } from "../../structures/common/workspaceRoot";
import { ParsedCoqFileData } from "../../structures/parsedCoqFile/parsedCoqFileData";
import { TheoremData } from "../../structures/parsedCoqFile/theoremData";
import { throwOnAbort } from "../../utils/asyncUtils/abortUtils";
import { AsyncScheduler } from "../../utils/asyncUtils/asyncScheduler";
import { reduceToMap } from "../../utils/collectionUtils/mapUtils";
import { hasAllPropertiesDefined } from "../../utils/objectUtils";
import {
    benchmarkingInvariantFailed,
    throwBenchmarkingError,
} from "../../utils/throwErrors";

import { CompletionGenerationTimeImpl, TimeMark } from "./measureTimeUtils";
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
    sourceTheorem: TheoremData;
    sourceFileEnvironment: SourceFileEnvironment;
    benchmarkingModelParams: BenchmarkingModelParams<ResolvedModelParams>;
    parentProofToFix: ParentProofToFix | undefined;
    nextGeneratedProofId: number;
    /**
     * The round number of the multiround completion generation process.
     * See `AbstractBenchmarkedCompletionGeneration.roundNumber`
     * and `GeneratedProof.versionNumber()` for more details.
     */
    roundNumber: number;
    llmService: LLMServiceType;
    llmServiceEventLogger: EventLogger;
    parsedSourceFileData: ParsedCoqFileData;
    workspaceRoot: WorkspaceRoot;
}

export interface ParentProofToFix {
    benchmarkedProof: ValidatedProof;
    diagnostic: string;
}

/**
 * Executes a _single_ round of completion generation and records the associated metrics.
 * This function performs only one iteration of a multiround generation process at a time.
 *
 * If proof generation fails due to the `llmService` being unavailable or unreachable (e.g., connection error),
 * the function will retry indefinitely by default or until `options.proofGenerationRetries` are reached / abort signal is sent.
 * The retries will occur with delays as specified in `LLMService.estimateTimeToBecomeAvailable` and `RemoteConnectionErrorDelays`,
 * until a response with proofs is received.
 *
 * Typically, this function does not throw errors:
 * expected errors are encapsulated within `FailedCompletionGeneration`.
 * However, the following exceptions will be handled differently:
 * - `ConfigurationError`-s and `FailFastAbortError`-s will always be rethrown;
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
    options: BenchmarkingOptions,
    modelsScheduler: AsyncScheduler,
    logger: BenchmarkingLogger,
    proofsChecker: AbstractProofsChecker,
    abortSignal: AbortSignal
): Promise<BenchmarkingResult> {
    // generate proofs
    const proofGenerationResult = await generateProofWithRetriesExclusively(
        generationArgs,
        options,
        modelsScheduler,
        logger,
        abortSignal
    );
    logger
        .asOneRecord()
        .info(
            `Successfully generated ${proofGenerationResult.proofs.length} proof(s)`
        )
        .debug(
            `Effective elapsed time: ${proofGenerationResult.effectiveElapsedTimeMillis} ms`,
            "gray"
        );
    const preparedProofsWithTokens: [
        string,
        GeneratedProof,
        GenerationTokens,
        number,
    ][] = proofGenerationResult.proofs.map(
        (proof: GeneratedProofItem, index: number) => [
            prepareProofToCheck(proof.generatedProof.proof()),
            proof.generatedProof,
            proof.tokensSpent,
            generationArgs.nextGeneratedProofId + index,
        ]
    );

    const measuredTime = new CompletionGenerationTimeImpl(
        proofGenerationResult.effectiveElapsedTimeMillis
    );
    const allGeneratedProofsMap = reduceToMap(
        preparedProofsWithTokens,
        ([preparedProof, _]) => preparedProof,
        ([preparedProof, generatedProof, tokens, generatedProofId]) =>
            new NonValidatedProof(
                generatedProof,
                preparedProof,
                tokens,
                generatedProofId
            )
    );

    // prepare result data
    const allGeneratedProofs = Array.from(allGeneratedProofsMap.values());
    const parsedSourceFile = generationArgs.parsedSourceFileData;
    const contextTheorems = proofGenerationResult.contextTheoremNames.map(
        (theoremName) =>
            parsedSourceFile.theoremsByNames.get(theoremName) ??
            invariantFailed(
                "Proof generation",
                `a context theorem with the name "${theoremName}" `,
                `was not found in the parsed data of the file ${parsedSourceFile.filePath}`
            )
    );
    const tokensSpentInTotal = proofGenerationResult.tokensSpentInTotal;
    const roundNumber = generationArgs.roundNumber;

    // check proofs
    throwOnAbort(abortSignal);
    let proofsCheckResult: ProofsCheckResult;
    try {
        proofsCheckResult = await proofsChecker.checkProofs(
            Array.from(allGeneratedProofsMap.keys()),
            generationArgs.completionContext,
            generationArgs.sourceFileEnvironment,
            generationArgs.workspaceRoot,
            logger,
            abortSignal
        );
    } catch (error) {
        if (error instanceof ProofsCheckFailedError) {
            logger.info(`Failed to validate proofs: ${error.causeMessage}`);
            return new FailedCompletionGenerationBenchmarking(
                allGeneratedProofs,
                contextTheorems,
                tokensSpentInTotal,
                measuredTime,
                roundNumber,
                {
                    failureType: error.failureType,
                    causeMessage: error.causeMessage,
                }
            );
        } else {
            throw error;
        }
    }
    // (!) TODO (mb): check proof-checker behaviour for the equal proofs
    const validatedProofs = proofsCheckResult.checkedProofs.map(
        (checkedProof) => {
            const nonValidatedProof =
                allGeneratedProofsMap.get(checkedProof.proof) ??
                illegalState(
                    `\`CoqProofChecker\` returned a proof that has not been sent as input`
                );
            return nonValidatedProof.validate(checkedProof);
        }
    );
    const allGeneratedProofsNumber = allGeneratedProofs.length;
    if (validatedProofs.length !== allGeneratedProofsNumber) {
        benchmarkingInvariantFailed(
            logger,
            "not all of the generated proofs were verified, ",
            "however the execution has not been aborted earlier;",
            `\nthere are ${allGeneratedProofsNumber - validatedProofs.length} generated proofs failed to be checked`
        );
    }

    measuredTime.addProofsValidationMillis(
        proofsCheckResult.effectiveElapsedMillis
    );
    const result = new SuccessfulCompletionGenerationBenchmarking(
        validatedProofs,
        contextTheorems,
        tokensSpentInTotal,
        measuredTime,
        roundNumber
    );
    logger
        .asOneRecord()
        .info(
            `Successfully verified proofs: ${result.thisRoundValidProofs.length} / ${allGeneratedProofsNumber} are valid`
        )
        .debug(
            `Effective elapsed time: ${proofsCheckResult.effectiveElapsedMillis} ms`,
            "gray"
        );
    return result;
}

namespace RemoteConnectionErrorDelays {
    export const initialDelayMillis = 10_000;
    export const exponentialMultiplier = 2;
}

interface ProofGenerationResult {
    proofs: GeneratedProofItem[];
    tokensSpentInTotal: GenerationTokens;
    contextTheoremNames: string[];
    effectiveElapsedTimeMillis: number;
}

interface GeneratedProofItem {
    generatedProof: GeneratedProof;
    // TODO (mb): document by referencing `GeneratedRawContentItem.tokensSpent`
    tokensSpent: GenerationTokens;
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
    options: BenchmarkingOptions,
    modelsScheduler: AsyncScheduler,
    logger: BenchmarkingLogger,
    abortSignal: AbortSignal
): Promise<ProofGenerationResult> {
    const benchmarkingParams = generationArgs.benchmarkingModelParams;
    return modelsScheduler.scheduleTask(async () => {
        let generateProof: (() => Promise<GeneratedProof[]>) | undefined =
            undefined;
        if (generationArgs.roundNumber === 0) {
            generateProof = async () => {
                const proofGenerationContext = buildProofGenerationContext(
                    generationArgs.completionContext,
                    generationArgs.sourceFileEnvironment.fileTheorems,
                    generationArgs.sourceTheorem.name,
                    benchmarkingParams.theoremRanker
                );
                return generationArgs.llmService.generateProof(
                    proofGenerationContext,
                    benchmarkingParams.modelParams,
                    benchmarkingParams.modelParams.defaultChoices,
                    ErrorsHandlingMode.RETHROW_ERRORS
                );
            };
        } else {
            generateProof = async () => {
                const parentProof =
                    generationArgs.parentProofToFix ??
                    illegalState(
                        `Proof-fix round should be performed (round number ${generationArgs.roundNumber} is > 0), `,
                        "but `parentProofToFix` is not provided"
                    );
                return await parentProof.benchmarkedProof.proofObject.fixProof(
                    parentProof.diagnostic,
                    benchmarkingParams.modelParams.multiroundProfile
                        .defaultProofFixChoices,
                    ErrorsHandlingMode.RETHROW_ERRORS
                );
            };
        }
        return generateProofWithRetriesMeasured(
            generateProof,
            generationArgs.llmService,
            generationArgs.llmServiceEventLogger,
            options,
            logger,
            abortSignal
        );
    }, logger);
}

async function generateProofWithRetriesMeasured(
    generateProofs: () => Promise<GeneratedProof[]>,
    llmService: LLMService<any, any>,
    llmServiceEventLogger: EventLogger,
    options: BenchmarkingOptions,
    logger: BenchmarkingLogger,
    abortSignal: AbortSignal
): Promise<ProofGenerationResult> {
    const result: Partial<ProofGenerationResult> = {};
    let generatedRawProofs: Map<string, GeneratedRawContentItem> | undefined =
        undefined;

    const succeededSubscriptionId = llmServiceEventLogger.subscribeToLogicEvent(
        LLMServiceImpl.requestSucceededEvent,
        (data: any) => {
            const request = data as LLMServiceRequestSucceeded;
            // (!!!) TODO (mb): pass logging object inside proof generation and get rid of tracking evens here
            generatedRawProofs = reduceToMap(
                request.generatedRawProofs,
                (item) =>
                    GeneratedProofImpl.removeProofQedIfNeeded(item.content),
                (item) => item
            );
            console.error(
                `\n\nBAKA BAKA:\n${request.generatedRawProofs.map((p) => p.content)}\n\n`
            );
            result.tokensSpentInTotal = request.tokensSpentInTotal;
            result.contextTheoremNames =
                request.analyzedChat?.contextTheorems ?? [];
        }
    );

    let delayMillis = 0;
    let prevFailureIsConnectionError = false;
    let attemptIndex = 0;

    let totalTime = new TimeMark();
    while (true) {
        // `options.proofGenerationRetries` might be undefined meaning the unlimited retries case
        if (attemptIndex === options.proofGenerationRetries) {
            throwBenchmarkingError(
                `Proof generation failed: max retries (${options.proofGenerationRetries}) has been reached`
            );
        }
        throwOnAbort(abortSignal);
        try {
            const attemptTime = new TimeMark();
            const generatedProofs = await generateProofs();
            result.proofs = generatedProofs.map((generatedProof) => {
                if (generatedRawProofs === undefined) {
                    benchmarkingInvariantFailed(logger, "event not received");
                }
                const rawProof =
                    generatedRawProofs.get(generatedProof.proof()) ??
                    illegalState(
                        `No proof logs in event for proof \`${generatedProof.proof()}\``
                    );
                return {
                    generatedProof: generatedProof,
                    tokensSpent: rawProof.tokensSpent,
                };
            });

            result.effectiveElapsedTimeMillis =
                attemptTime.measureElapsedMillis();
            if (!hasAllPropertiesDefined<ProofGenerationResult>(result)) {
                invariantFailed(
                    "Proof generation",
                    "proofs were generated, but a request-succeeded event was not sent"
                );
            }

            const tokens = result.tokensSpentInTotal;
            logger
                .asOneRecord()
                .debug(
                    `Attempt #${attemptIndex}, successfully generated proofs`
                )
                .debug(
                    `Tokens spent: ${tokens.tokensSpentInTotal} = ${tokens.promptTokens} (prompt) + ${tokens.generatedTokens} (generated answer)`
                )
                .debug(
                    `Total elapsed time of all ${attemptIndex + 1} attempt(s): ${millisToString(totalTime.measureElapsedMillis())}`
                );
            if (options.logTeamCityStatistics) {
                writeTeamCityStatisticsValue(
                    "spentTokens",
                    tokens.tokensSpentInTotal
                );
            }

            llmServiceEventLogger.unsubscribe(
                LLMServiceImpl.requestSucceededEvent,
                succeededSubscriptionId
            );

            return result;
        } catch (e) {
            if (!(e instanceof LLMServiceError)) {
                illegalState(
                    "`LLMService` is expected to throw only `LLMServiceError`-s ",
                    `but got:\n${buildErrorCompleteLog(e)}`
                );
            }
            const llmServiceError = e as LLMServiceError;

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
                illegalState(
                    `unknown \`LLMServiceError\` type: ${llmServiceError.name};\n`,
                    buildErrorCompleteLog(llmServiceError)
                );
            }
            // wait and try again
            await delay(delayMillis, abortSignal);
            attemptIndex += 1;
        }
    }
}

/**
 * _Important:_ this function is the one responsbile for **removing
 * the target theorem from the context** (i.e. file theorems) if it is present there.
 */
function buildProofGenerationContext(
    completionContext: CompletionContext,
    fileTheorems: Theorem[],
    targetTheoremName: string,
    theoremRanker?: ContextTheoremsRanker
): ProofGenerationContext {
    const contextTheorems = fileTheorems.filter(
        (theorem) => theorem.name !== targetTheoremName
    );
    const rankedTheorems =
        theoremRanker?.rankContextTheorems(
            contextTheorems,
            completionContext
        ) ?? fileTheorems;
    return {
        contextTheorems: rankedTheorems,
        completionTarget: goalToTargetLemma(completionContext.proofGoal),
    };
}
