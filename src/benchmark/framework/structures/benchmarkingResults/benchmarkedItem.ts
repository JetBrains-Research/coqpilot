import { GenerationTokens } from "../../../../llm/llmServices/commonStructures/generationTokens";

import { BenchmarkingItem } from "../benchmarkingCore/benchmarkingItem";
import { TheoremData } from "../parsedCoqFile/theoremData";

import {
    BenchmarkedProof,
    NonValidatedProof,
    ValidatedProof,
} from "./benchmarkedProof";

export interface BenchmarkedItem {
    item: BenchmarkingItem;
    result: BenchmarkingResult;
}

export type BenchmarkingResult =
    | FailedCompletionGenerationBenchmarking
    | SuccessfulCompletionGenerationBenchmarking;

type BenchmarkedCompletionGeneration =
    AbstractBenchmarkedCompletionGeneration<BenchmarkedProof>;

abstract class AbstractBenchmarkedCompletionGeneration<
    ProofType extends BenchmarkedProof,
> {
    constructor(
        readonly generatedProofs: ProofType[],
        readonly contextTheorems: TheoremData[],
        /**
         * Tokens spent to generate `allGeneratedProofs` in total.
         * To access per-proof tokens metrics, use `MeasuredProof.chatTokens` property.
         *
         * However, these metrics might be just an approximate estimation of the real ones.
         * Check `GeneratedRawContent.tokensSpentInTotal` for more details.
         */
        readonly tokensSpentInTotal: GenerationTokens,
        readonly elapsedTime: CompletionGenerationTime,
        // TODO (mb): document
        readonly round: number
    ) {}

    isFailedToFinishRound(): this is FailedCompletionGenerationBenchmarking {
        const maybeFailedToFinish =
            this as unknown as FailedCompletionGenerationBenchmarking;
        return maybeFailedToFinish.failureMetadata !== undefined;
    }

    isSuccessfullyFinishedRound(): this is SuccessfulCompletionGenerationBenchmarking {
        return !this.isFailedToFinishRound();
    }

    /**
     * Traverses all results of the rounds in the BFS order.
     * Namely, `this` round will be visited first,
     * then all results obtained for the next one, and so on.
     *
     * If there is only single round, this method returns `[this]`;
     */
    getAllRoundsResults(): BenchmarkedCompletionGeneration[] {
        const traversal = [];

        let lastRoundTraversal: BenchmarkedCompletionGeneration[] = [this];

        while (lastRoundTraversal.length !== 0) {
            traversal.push(...lastRoundTraversal);
            const nextRoundTraversal = [];
            for (const parentRound of lastRoundTraversal) {
                if (parentRound.isSuccessfullyFinishedRound()) {
                    const childResults = parentRound.generatedProofs
                        .map((proof) => proof.nextRoundResult)
                        .filter((result) => result !== undefined);
                    nextRoundTraversal.push(...childResults);
                }
            }
            lastRoundTraversal = nextRoundTraversal;
        }

        return traversal;
    }

    /**
     * Traverses all generated proofs in the BFS order.
     * Namely, first all the proofs generated in `this` round will be visited,
     * then all generated in the next one, and so on.
     *
     * If there is only single round, this method returns the same as `this.allGeneratedProofs`;
     */
    getAllProofsByRounds(): BenchmarkedProof[] {
        return this.getAllRoundsResults().flatMap(
            (roundResult) => roundResult.generatedProofs
        );
    }

    getAllValidProofs(): ValidatedProof[] {
        return this.getAllProofsByRounds().filter(
            (proof) => proof.isValidated() && proof.validationResult.isValid
        ) as ValidatedProof[];
    }

    isSuccessfulCompletion(): boolean {
        return this.getAllValidProofs().length > 0;
    }

    getAllFailedToFinishRounds(): FailedCompletionGenerationBenchmarking[] {
        return this.getAllRoundsResults().filter((roundResult) =>
            roundResult.isFailedToFinishRound()
        );
    }

    hasFailedToFinish(): boolean {
        return this.getAllFailedToFinishRounds().length !== 0;
    }

    hasSuccessfullyFinished(): boolean {
        return this.getAllFailedToFinishRounds().length === 0;
    }
}

export interface CompletionGenerationTime {
    proofsGenerationMillis: number;
    proofsValidationMillis: number | undefined;
    totalMillis: number;
}

export class FailedCompletionGenerationBenchmarking extends AbstractBenchmarkedCompletionGeneration<NonValidatedProof> {
    constructor(
        generatedProofs: NonValidatedProof[],
        contextTheorems: TheoremData[],
        tokensSpentInTotal: GenerationTokens,
        elapsedTime: CompletionGenerationTime,
        round: number,
        readonly failureMetadata: FailureMetadata
    ) {
        super(
            generatedProofs,
            contextTheorems,
            tokensSpentInTotal,
            elapsedTime,
            round
        );
    }
}

// TODO: document better
// configuration or unexpected error => not a result at all, should be thrown & reported
export interface FailureMetadata {
    failureType: FailureType;
    causeMessage: string;
}

export type FailureType = "COQ_LSP_TIMEOUT" | "COQ_PROOF_CHECKER_ERROR";

export class SuccessfulCompletionGenerationBenchmarking extends AbstractBenchmarkedCompletionGeneration<ValidatedProof> {
    constructor(
        generatedProofs: ValidatedProof[],
        contextTheorems: TheoremData[],
        tokensSpentInTotal: GenerationTokens,
        elapsedTime: CompletionGenerationTime,
        round: number
    ) {
        super(
            generatedProofs,
            contextTheorems,
            tokensSpentInTotal,
            elapsedTime,
            round
        );
    }

    get thisRoundValidProofs(): ValidatedProof[] {
        return this.generatedProofs.filter(
            (proof) => proof.validationResult.isValid
        );
    }

    get thisRoundNonValidProofs(): ValidatedProof[] {
        return this.generatedProofs.filter(
            (proof) => !proof.validationResult.isValid
        );
    }
}
