import {
    CompletionGenerationTime,
    MeasuredProof,
} from "../structures/benchmarkedItem";
import { LengthMetrics } from "../structures/utilStructures";

export async function measureElapsedMillis<T>(
    block: () => Promise<T>
): Promise<[T, number]> {
    const startTime = performance.now();
    const result = await block();
    const endTime = performance.now();
    return [result, Math.round(endTime - startTime)];
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

export class MeasuredProofImpl implements MeasuredProof {
    constructor(readonly asString: string) {}

    readonly length = measureLength(this.asString);
}
