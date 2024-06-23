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
