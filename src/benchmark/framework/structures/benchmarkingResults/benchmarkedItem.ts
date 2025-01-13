import { GenerationTokens } from "../../../../llm/llmServices/commonStructures/generationTokens";
import { GeneratedProof } from "../../../../llm/llmServices/generatedProof";

import { BenchmarkingItem } from "../benchmarkingCore/benchmarkingItem";
import { LengthMetrics } from "../common/measureStructures";
import { TheoremData } from "../parsedCoqFile/theoremData";

export interface BenchmarkedItem {
    item: BenchmarkingItem;
    result: BenchmarkedCompletionGeneration;
}

export interface BenchmarkedCompletionGeneration {
    allGeneratedProofs: ValidatedProof[];
    contextTheorems: TheoremData[];
    /**
     * Tokens spent to generate `allGeneratedProofs` in total.
     * To access per-proof tokens metrics, use `MeasuredProof.chatTokens` property.
     *
     * However, these metrics might be just an approximate estimation of the real ones.
     * Check `GeneratedRawContent.tokensSpentInTotal` for more details.
     */
    tokensSpentInTotal: GenerationTokens;
    elapsedTime: CompletionGenerationTime;

    // TODO (mb): document
    round: number;
}

export interface ValidatedProof extends MeasuredProof {
    generatedProof: GeneratedProof;
    // TODO (mb): document; undefine means not validated yet
    validation: ValidationResult | undefined;
    nextProofFixRound: BenchmarkedCompletionGeneration | undefined;
}

export interface ValidationResult {
    isValid: boolean;
    diagnostic: string | undefined;
}

export interface MeasuredProof {
    asString: string;
    length: LengthMetrics;
    /**
     * Tokens spent to generate this specific proof.
     *
     * **Warning:** most likely, these metrics might be just an approximate estimation of the real ones.
     * To get probably more accurate (but aggregated) data,
     * use `BenchmarkedCompletionGeneration.tokensSpentInTotal` instead (check its docs for more details).
     */
    tokensSpent: GenerationTokens;
}

export interface CompletionGenerationTime {
    proofsGenerationMillis: number;
    proofsValidationMillis: number | undefined;
    totalMillis: number;
}

export interface SuccessfulCompletionGeneration
    extends BenchmarkedCompletionGeneration {
    validProofs: MeasuredProof[];
}

export function isSuccessfulGeneration(
    result: BenchmarkedCompletionGeneration
): result is SuccessfulCompletionGeneration {
    return (result as SuccessfulCompletionGeneration).validProofs !== undefined;
}

export interface FailedCompletionGeneration
    extends BenchmarkedCompletionGeneration {
    failureType: CompletionGenerationFailureType;
    causeMessage: string;
    // configuration or unexpected => (not a result, report)
    // TODO: document better
}

// TODO: update them accordingly to the new coq-lsp
export enum CompletionGenerationFailureType {
    SEARCH_FAILED,
    TIMEOUT, // TODO: coq proof checker / coq lsp timeout?
    COQ_PROOF_CHECKER_ERROR,
}

export function isFailedGeneration(
    result: BenchmarkedCompletionGeneration
): result is FailedCompletionGeneration {
    const maybeFailedGeneration = result as FailedCompletionGeneration;
    return (
        maybeFailedGeneration.failureType !== undefined &&
        maybeFailedGeneration.causeMessage !== undefined
    );
}
