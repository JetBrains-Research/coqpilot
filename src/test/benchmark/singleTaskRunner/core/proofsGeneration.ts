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
} from "../../../../core/completionGenerationContext";
import { ContextTheoremsRanker } from "../../../../core/contextTheoremRanker/contextTheoremsRanker";
import { goalToTargetLemma } from "../../../../core/exposedCompletionGeneratorUtils";

import { TimeMark } from "../../../../benchmark/framework/benchmarkCompletionGeneration/measureUtils";
import { BenchmarkingLogger } from "../../../../benchmark/framework/logging/benchmarkingLogger";
import { BenchmarkingModelParams } from "../../../../benchmark/framework/structures/benchmarkingModelParams";
import { Theorem } from "../../../../coqParser/parsedTypes";
import { stringifyAnyValue } from "../../../../utils/printers";
import { delay } from "../../../commonTestFunctions/delay";

export namespace ProofsGeneration {
    namespace RemoteConnectionErrorDelays {
        export const initialDelayMillis = 10000;
        export const exponentialMultiplier = 2;
    }

    export async function generateProofWithRetriesMeasured<
        ResolvedModelParams extends ModelParams,
    >(
        completionContext: CompletionContext,
        sourceFileEnvironment: SourceFileEnvironment,
        benchmarkingModelParams: BenchmarkingModelParams<ResolvedModelParams>,
        llmService: LLMService<any, any>,
        requestLLMServiceMaxRetries: number,
        logger: BenchmarkingLogger
    ): Promise<[GeneratedProof[], number]> {
        let delayMillis = 0;
        let prevFailureIsConnectionError = false;
        let totalTime = new TimeMark();
        for (
            let attempt = 0;
            attempt < requestLLMServiceMaxRetries;
            attempt++
        ) {
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
                    .debug(`Attempt #${attempt}, successfully generated proofs`)
                    .debug(
                        `Total elapsed time (all ${attempt + 1} attempts): ${millisToString(totalTime.measureElapsedMillis())}`
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
                        `Attempt #${attempt}, configuration error: ${stringifyAnyValue(llmServiceError.message)}`
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
                            `Attempt #${attempt}, generation failed error: ${stringifyAnyValue(llmServiceError.message)}`
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
                            `Attempt #${attempt}, remote connection error: ${stringifyAnyValue(llmServiceError.message)}`
                        )
                        .debug(
                            `Delay to wait for: ${millisToString(delayMillis)}`
                        );
                } else {
                    // TODO: serialize more carefully than just stack
                    throw Error(
                        `unknown \`LLMServiceError\` type: ${stringifyAnyValue(llmServiceError.name)}, ${llmServiceError.stack}`
                    );
                }
                // wait and try again
                await delay(delayMillis);
            }
        }
        throw Error(
            `Failed to access "${llmService.serviceName}" service: max retries of proof-generation requests have been performed`
        );
    }

    function buildProofGenerationContext(
        completionContext: CompletionContext,
        fileTheorems: Theorem[],
        theoremRanker?: ContextTheoremsRanker
    ): ProofGenerationContext {
        const rankedTheorems =
            theoremRanker?.rankContextTheorems(
                fileTheorems,
                completionContext
            ) ?? fileTheorems;
        return {
            contextTheorems: rankedTheorems,
            completionTarget: goalToTargetLemma(completionContext.proofGoal),
        };
    }
}
