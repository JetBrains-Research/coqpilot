import { GenerationTokens } from "../../../../llm/llmServices/commonStructures/generationTokens";
import { GeneratedProof } from "../../../../llm/llmServices/generatedProof";

import { ProofCheckResult } from "../../../../core/coqProofChecker";

import {
    BenchmarkedCompletionGeneration,
    CompletionGenerationTime,
    ValidatedProof,
    ValidationResult,
} from "../../structures/benchmarkingResults/benchmarkedItem";
import { LengthMetrics } from "../../structures/common/measureStructures";

export async function measureElapsedMillis<T>(
    block: () => Promise<T>
): Promise<[T, number]> {
    const timeMark = new TimeMark();
    const result = await block();
    return [result, timeMark.measureElapsedMillis()];
}

export function measureLength(proof: string): LengthMetrics {
    return {
        inSymbols: proof.length,
        inSteps: proof.split(".").length, // TODO: check and perform more accurately
        inTokens: undefined, // TODO
    };
}

export class CompletionGenerationTimeImpl implements CompletionGenerationTime {
    totalMillis: number;
    proofsValidationMillis: number | undefined;

    constructor(readonly proofsGenerationMillis: number) {
        this.totalMillis = proofsGenerationMillis;
        this.proofsValidationMillis = undefined;
    }

    addProofsValidationMillis(millis: number) {
        this.proofsValidationMillis = millis;
        this.totalMillis += millis;
    }
}

// TODO (mb): remove after finishing the developing other interfaces
// export class MeasuredProofImpl implements MeasuredProof {
//     constructor(
//         readonly asString: string,
//         readonly tokensSpent: GenerationTokens
//     ) {}

//     readonly length = measureLength(this.asString);
// }

export class ValidatedProofImpl implements ValidatedProof {
    constructor(
        readonly generatedProof: GeneratedProof,
        readonly asString: string,
        readonly tokensSpent: GenerationTokens
    ) {}

    readonly length = measureLength(this.asString);

    validation: ValidationResult | undefined;
    nextProofFixRound: BenchmarkedCompletionGeneration | undefined = undefined;

    setCheckResult(checkedProof: ProofCheckResult) {
        this.validation = {
            isValid: checkedProof.isValid,
            diagnostic: checkedProof.diagnostic,
        };
    }
}

export class TimeMark {
    private startTime: number;

    constructor() {
        this.startTime = performance.now();
    }

    measureElapsedMillis(): number {
        return Math.round(performance.now() - this.startTime);
    }
}
