import {
    ConfigurationError,
    GenerationFailedError,
    LLMServiceError,
    RemoteConnectionError,
} from "../../../../llm/llmServiceErrors";
import { GenerationTokens } from "../../../../llm/llmServices/commonStructures/generationTokens";
import { ProofGenerationMetadataHolder } from "../../../../llm/llmServices/commonStructures/proofGenerationMetadata";
import { GeneratedProof } from "../../../../llm/llmServices/generatedProof";
import { LLMService } from "../../../../llm/llmServices/llmService";
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
import { infinitySymbol } from "../../logging/specialSymbols";
import { BenchmarkingModelParams } from "../../structures/benchmarkingCore/benchmarkingModelParams";
import { BenchmarkingOptions } from "../../structures/benchmarkingCore/benchmarkingOptions";
import {
    BenchmarkingResult,
    FailedCompletionGenerationBenchmarking,
    SuccessfulCompletionGenerationBenchmarking,
    translateToFailureType,
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
import { groupByAndMap } from "../../utils/collectionUtils/mapUtils";
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
 * The function handles errors as follows:
 * - throws a `BenchmarkingError` if proof generation fails within the configured `proofGenerationRetries` attempts;
 * - captures proof-checking errors, such as proof-check timeouts or `CoqProofChecker` failures,
 *   within `FailedCompletionGenerationBenchmarking`.
 *
 * However, the following exceptions are always rethrown:
 * - `ConfigurationError`: notifies the user immediately about incorrect pipeline configuration;
 * - `FailFastAbortError`: halts execution in response to a fail-fast strategy signal;
 * - `IllegalStateError`: indicates internal invariant violations that may lead to unexpected behavior;
 * - any other unexpected errors are wrapped into an `IllegalStateError`, indicating an illegal state.
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
    const preparedProofs: [string, GeneratedProof, number][] =
        proofGenerationResult.generatedProofs.map(
            (generatedProof: GeneratedProof, index: number) => [
                prepareProofToCheck(generatedProof.proof),
                generatedProof,
                generationArgs.nextGeneratedProofId + index,
            ]
        );

    const measuredTime = new CompletionGenerationTimeImpl(
        proofGenerationResult.effectiveElapsedTimeMillis
    );
    // Generated `preparedProofs` _might_ contain duplicate proofs;
    // therefore, any further mappings should be done carefully,
    // so as not to lose duplicate proofs objects.
    // Their metadata might be different despite the same string representation and
    // in any case they are important for showing the correct number of tokens spent in total;
    // therefore, duplicates must be saved.
    const allGeneratedProofsMap = groupByAndMap(
        preparedProofs,
        ([preparedProof, _]) => preparedProof,
        ([preparedProof, generatedProof, generatedProofId]) =>
            new NonValidatedProof(
                generatedProof,
                preparedProof,
                generatedProofId
            )
    );

    // prepare result data
    const allGeneratedProofs = Array.from(
        allGeneratedProofsMap.values()
    ).flat();
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
        // Although `CoqProofChecher.checkProofs(...)` allows duplicate proofs
        // (and returns duplicate `ProofCheckResult`-s for them),
        // this behaviour could be changed in the future.
        // Therefore, the following code handles proofs duplicates by itself.
        proofsCheckResult = await proofsChecker.checkProofs(
            Array.from(allGeneratedProofsMap.keys()),
            generationArgs.completionContext,
            generationArgs.sourceFileEnvironment,
            generationArgs.workspaceRoot,
            options.proofCheckTimeoutMillis,
            logger,
            abortSignal
        );
    } catch (error) {
        if (error instanceof ProofsCheckFailedError) {
            const failureType = translateToFailureType(error.failureType);
            logger
                .asOneRecord()
                .info(`Failed to validate proofs: ${failureType}`)
                .debug(`Cause: ${error.causeMessage}`);
            return new FailedCompletionGenerationBenchmarking(
                allGeneratedProofs,
                contextTheorems,
                tokensSpentInTotal,
                measuredTime,
                roundNumber,
                {
                    failureType: failureType,
                    causeMessage: error.causeMessage,
                }
            );
        } else {
            // Potential bug (!): all unexpected errors should be wrapped into
            // IllegalsStateError - it should be checked here and performed
            throw error;
        }
    }
    const validatedProofs = proofsCheckResult.checkedProofs.flatMap(
        (checkedProof) => {
            const nonValidatedProofs =
                allGeneratedProofsMap.get(checkedProof.proof) ??
                illegalState(
                    `\`CoqProofChecker\` returned a proof that has not been sent as input`
                );
            return nonValidatedProofs.map((proof) =>
                proof.validate(checkedProof)
            );
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
        proofsCheckResult.totalEffectiveElapsedMillis
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
            `Proof-check effective elapsed time: ${proofsCheckResult.proofCheckElapsedMillis} ms`,
            "gray"
        )
        .debug(
            `Proof-check & \`coq-lsp\` setup effective elapsed time: ${proofsCheckResult.totalEffectiveElapsedMillis} ms`,
            "gray"
        );
    return result;
}

/**
 * Prevents from buggy delay estimates:
 * infinite cycle with zero delays might cause some troubles.
 */
export const minDelayMillis = 100;

namespace RemoteConnectionErrorDelays {
    export const initialDelayMillis = 10_000;
    export const exponentialMultiplier = 2;
}

interface ProofGenerationResult {
    generatedProofs: GeneratedProof[];
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
    generationArgs: CompletionGenerationBenchmarkArgs<
        ResolvedModelParams,
        LLMService<any, ResolvedModelParams>
    >,
    options: BenchmarkingOptions,
    modelsScheduler: AsyncScheduler,
    logger: BenchmarkingLogger,
    abortSignal: AbortSignal
): Promise<ProofGenerationResult> {
    const benchmarkingParams = generationArgs.benchmarkingModelParams;
    return modelsScheduler.scheduleTask(async () => {
        let generateProof:
            | ((
                  metadataHolder: ProofGenerationMetadataHolder
              ) => Promise<GeneratedProof[]>)
            | undefined = undefined;
        if (generationArgs.roundNumber === 1) {
            generateProof = async (metadataHolder) => {
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
                    metadataHolder
                );
            };
        } else {
            generateProof = async (metadataHolder) => {
                const parentProof =
                    generationArgs.parentProofToFix ??
                    illegalState(
                        `Proof-fix round should be performed (round number ${generationArgs.roundNumber} is > 1), `,
                        "but `parentProofToFix` is not provided"
                    );
                return await parentProof.benchmarkedProof.proofObject.fixProof(
                    parentProof.diagnostic,
                    benchmarkingParams.modelParams.multiroundProfile
                        .defaultProofFixChoices,
                    metadataHolder
                );
            };
        }
        return generateProofWithRetriesMeasured(
            generateProof,
            generationArgs.llmService,
            options,
            generationArgs.roundNumber,
            logger,
            abortSignal
        );
    }, logger);
}

async function generateProofWithRetriesMeasured(
    generateProofs: (
        metadataHolder: ProofGenerationMetadataHolder
    ) => Promise<GeneratedProof[]>,
    llmService: LLMService<any, any>,
    options: BenchmarkingOptions,
    roundNumber: number,
    logger: BenchmarkingLogger,
    abortSignal: AbortSignal
): Promise<ProofGenerationResult> {
    let delayMillis = 0;
    let prevFailureIsConnectionError = false;
    let attemptIndex = 1;
    const maxAttemptsString = options.proofGenerationRetries ?? infinitySymbol;

    let totalTime = new TimeMark();
    while (true) {
        const attemptLogger = logger.createChildLoggerWithIdentifier(
            `[proof generation attempt ${attemptIndex}/${maxAttemptsString}]`
        );
        // `options.proofGenerationRetries` might be undefined meaning the unlimited retries case
        if (attemptIndex - 1 === options.proofGenerationRetries) {
            attemptLogger.error(
                `max retries (${options.proofGenerationRetries}) has been reached`,
                "default"
            );
            throwBenchmarkingError(
                `Proof generation failed: max retries (${options.proofGenerationRetries}) `,
                `has been reached at round ${roundNumber}`
            );
        }
        throwOnAbort(abortSignal);
        try {
            const attemptTime = new TimeMark();

            const metadataHolder = new ProofGenerationMetadataHolder();
            const generatedProofs = await generateProofs(metadataHolder);
            const successMetadata =
                metadataHolder.getSuccessfulProofGenerationMetadata();

            const result: ProofGenerationResult = {
                generatedProofs: generatedProofs,
                tokensSpentInTotal: successMetadata.tokensSpentInTotal,
                contextTheoremNames:
                    successMetadata.analyzedChat?.contextTheorems ?? [],
                effectiveElapsedTimeMillis: attemptTime.measureElapsedMillis(),
            };

            const tokens = result.tokensSpentInTotal;
            attemptLogger
                .asOneRecord()
                .info(
                    `Successfully generated ${generatedProofs.length} proof(s)`
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
                attemptLogger.error(
                    `Configuration error: ${llmServiceError.message}`,
                    "default"
                );
                throw llmServiceError;
            }
            if (llmServiceError instanceof GenerationFailedError) {
                const estimatedTime =
                    llmService.estimateTimeToBecomeAvailable();
                delayMillis = Math.max(
                    timeToMillis(estimatedTime),
                    minDelayMillis
                );
                attemptLogger
                    .asOneRecord()
                    .debug(
                        `Generation failed error: ${llmServiceError.message}`
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
                attemptLogger
                    .asOneRecord()
                    .debug(
                        `Remote connection error: ${stringifyAnyValue(llmServiceError.message)}`
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
