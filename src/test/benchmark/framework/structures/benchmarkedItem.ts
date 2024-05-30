import { BenchmarkingItem } from "./benchmarkingItem";
import {
    EstimatedChatTokens,
    LengthMetrics,
    TheoremData,
} from "./utilStructures";

export interface BenchmarkedItem {
    item: BenchmarkingItem;
    result: BenchmarkedCompletionGeneration;
}

export interface BenchmarkedCompletionGeneration {
    allGeneratedCompletions: Completion[];
    elapsedTimeMillis: number;
    contextTheorems: TheoremData[] | undefined;
    chatTokens: EstimatedChatTokens | undefined;
}

export interface SuccessfulCompletionGeneration
    extends BenchmarkedCompletionGeneration {
    validCompletions: Completion[];
}

export interface FailedCompletionGeneration
    extends BenchmarkedCompletionGeneration {
    failureType: CompletionGenerationFailureType;
    causeMessage: string;
    // configuration or unexpected => (not a result, report)
}

export interface Completion {
    asString: string;
    length: LengthMetrics;
}

export enum CompletionGenerationFailureType {
    SEARCH_FAILED,
    TIMEOUT, // coq proof checker / coq lsp timeout?
    COQ_PROOF_CHECKER_ERROR,
}
