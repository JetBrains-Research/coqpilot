import { BenchmarkingItem } from "./benchmarkingItem";
import { TheoremData } from "./theoremData";
import { EstimatedChatTokens, LengthMetrics } from "./utilStructures";

export interface BenchmarkedItem {
    item: BenchmarkingItem;
    result: BenchmarkedCompletionGeneration;
}

export interface BenchmarkedCompletionGeneration {
    allGeneratedProofs: MeasuredProof[];
    elapsedTime: CompletionGenerationTime;
    contextTheorems: TheoremData[] | undefined;
    chatTokens: EstimatedChatTokens | undefined;
}

export interface MeasuredProof {
    asString: string;
    length: LengthMetrics;
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
}

export enum CompletionGenerationFailureType {
    SEARCH_FAILED,
    TIMEOUT, // coq proof checker / coq lsp timeout?
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
