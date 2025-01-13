import { GenerationTokens } from "../../../../llm/llmServices/commonStructures/generationTokens";
import { GeneratedProof } from "../../../../llm/llmServices/generatedProof";

import { ProofCheckResult } from "../../../../core/coqProofChecker";

import { LengthMetrics } from "../common/measureStructures";

import { BenchmarkingResult } from "./benchmarkedItem";

export type BenchmarkedProof = NonValidatedProof | ValidatedProof;

abstract class AbstractBenchmarkedProof {
    constructor(
        readonly proofObject: GeneratedProof,
        readonly asString: string,
        /**
         * Tokens spent to generate this specific proof.
         *
         * **Warning:** most likely, these metrics might be just an approximate estimation of the real ones.
         * To get probably more accurate (but aggregated) data,
         * use `BenchmarkedCompletionGeneration.tokensSpentInTotal` instead (check its docs for more details).
         */
        readonly tokensSpent: GenerationTokens
    ) {}

    readonly length = measureLength(this.asString);

    isValidated(): this is ValidatedProof {
        const maybeValidatedProof = this as unknown as ValidatedProof;
        return maybeValidatedProof.isValidated !== undefined;
    }
}

export function measureLength(proof: string): LengthMetrics {
    return {
        inSymbols: proof.length,
        inSteps: proof.split(".").length, // TODO: check and perform more accurately
        inTokens: undefined, // TODO
    };
}

export class NonValidatedProof extends AbstractBenchmarkedProof {
    constructor(
        proofObject: GeneratedProof,
        asString: string,
        tokensSpent: GenerationTokens
    ) {
        super(proofObject, asString, tokensSpent);
    }

    validate(checkedProof: ProofCheckResult): ValidatedProof {
        const validationResult: ValidationResult = {
            isValid: checkedProof.isValid,
            diagnostic: checkedProof.diagnostic,
        };
        return new ValidatedProof(
            this.proofObject,
            this.asString,
            this.tokensSpent,
            validationResult
        );
    }
}

export class ValidatedProof extends AbstractBenchmarkedProof {
    constructor(
        proofObject: GeneratedProof,
        asString: string,
        tokensSpent: GenerationTokens,
        readonly validationResult: ValidationResult
    ) {
        super(proofObject, asString, tokensSpent);
    }

    private nextProofFixRoundResult: BenchmarkingResult | undefined = undefined;

    get nextRoundResult(): BenchmarkingResult | undefined {
        return this.nextProofFixRoundResult;
    }

    linkNextRoundResult(proofFixRoundResult: BenchmarkingResult) {
        this.nextProofFixRoundResult = proofFixRoundResult;
    }
}

export interface ValidationResult {
    isValid: boolean;
    diagnostic: string | undefined;
}
