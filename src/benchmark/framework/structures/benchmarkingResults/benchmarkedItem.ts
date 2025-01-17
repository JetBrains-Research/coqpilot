import { GenerationTokens } from "../../../../llm/llmServices/commonStructures/generationTokens";

import { addToTotalTime } from "../../benchmarkingCore/singleCompletionGeneration/measureTimeUtils";
import { ProofsCheckFailureType } from "../../benchmarkingCore/singleCompletionGeneration/proofsCheckers/abstractProofsChecker";
import { BenchmarkingItem } from "../benchmarkingCore/benchmarkingItem";
import { TheoremData } from "../parsedCoqFile/theoremData";

import {
    BenchmarkedProof,
    NonValidProof,
    NonValidatedProof,
    ValidProof,
    ValidatedProof,
} from "./benchmarkedProof";

export interface BenchmarkedItem {
    item: BenchmarkingItem;
    result: BenchmarkingResult;
}

export type BenchmarkingResult =
    | SuccessfulCompletionGenerationBenchmarking
    | FailedCompletionGenerationBenchmarking;

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
        readonly roundElapsedTime: CompletionGenerationTime,
        /**
         * The round number of the multiround completion generation process.
         * This corresponds to the version number of the proofs
         * generated during this round (see `GeneratedProof.versionNumber()`).
         * Specifically, the first round of proof generation (i.e., the root round) has `roundNumber: 1`.
         * Each subsequent round, corresponding to proof fixing, increments the round number by 1.
         */
        readonly roundNumber: number
    ) {}

    private _parentProofToFixId: number | undefined = undefined;

    get parentProofToFixId(): number | undefined {
        return this._parentProofToFixId;
    }

    linkParentProofToFix(parentProofToFix: ValidatedProof) {
        this._parentProofToFixId = parentProofToFix.generatedProofId;
    }

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
    getAllRoundsResults(): BenchmarkingResult[] {
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

        return traversal as BenchmarkingResult[];
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
            (roundResult) => roundResult.generatedProofs as BenchmarkedProof[]
        );
    }

    getAllValidProofs(): ValidProof[] {
        return this.getAllProofsByRounds().filter(
            (proof) => proof.isValidated() && proof.isValidProof()
        );
    }

    // TODO: can be cached and updated only on linking
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

    getTotalElapsedTime(): CompletionGenerationTime {
        return this.getAllRoundsResults().reduce(
            (totalTime: CompletionGenerationTime, roundResult) =>
                addToTotalTime(totalTime, roundResult.roundElapsedTime),
            {
                proofsGenerationMillis: 0,
                proofsValidationMillis: 0,
                totalMillis: 0,
            } as CompletionGenerationTime
        );
    }
}

export interface CompletionGenerationTime {
    proofsGenerationMillis: number;
    proofsValidationMillis: number | undefined;
    totalMillis: number;
}

export class SuccessfulCompletionGenerationBenchmarking extends AbstractBenchmarkedCompletionGeneration<ValidatedProof> {
    constructor(
        generatedProofs: ValidatedProof[],
        contextTheorems: TheoremData[],
        tokensSpentInTotal: GenerationTokens,
        roundElapsedTime: CompletionGenerationTime,
        roundNumber: number
    ) {
        super(
            generatedProofs,
            contextTheorems,
            tokensSpentInTotal,
            roundElapsedTime,
            roundNumber
        );
    }

    get thisRoundValidProofs(): ValidProof[] {
        return this.generatedProofs.filter((proof) => proof.isValidProof());
    }

    get thisRoundNonValidProofs(): NonValidProof[] {
        return this.generatedProofs.filter((proof) => proof.isNonValidProof());
    }
}

export class FailedCompletionGenerationBenchmarking extends AbstractBenchmarkedCompletionGeneration<NonValidatedProof> {
    constructor(
        generatedProofs: NonValidatedProof[],
        contextTheorems: TheoremData[],
        tokensSpentInTotal: GenerationTokens,
        roundElapsedTime: CompletionGenerationTime,
        roundNumber: number,
        readonly failureMetadata: FailureMetadata
    ) {
        super(
            generatedProofs,
            contextTheorems,
            tokensSpentInTotal,
            roundElapsedTime,
            roundNumber
        );
    }
}

// TODO: document better
// configuration or unexpected error => not a result at all, should be thrown & reported
export interface FailureMetadata {
    failureType: FailureType;
    causeMessage: string;
}

export type FailureType = "`coq-lsp` timeout" | "`CoqProofChecker` error";

export function translateToFailureType(
    failureType: ProofsCheckFailureType
): FailureType {
    switch (failureType) {
        case "COQ_LSP_TIMEOUT":
            return "`coq-lsp` timeout";
        case "COQ_PROOF_CHECKER_ERROR":
            return "`CoqProofChecker` error";
    }
}
