import { CompletionGenerationTime } from "../../structures/benchmarkingResults/benchmarkedItem";

export async function measureElapsedMillis<T>(
    block: () => Promise<T>
): Promise<[T, number]> {
    const timeMark = new TimeMark();
    const result = await block();
    return [result, timeMark.measureElapsedMillis()];
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

export class TimeMark {
    private startTime: number;

    constructor() {
        this.startTime = performance.now();
    }

    measureElapsedMillis(): number {
        return Math.round(performance.now() - this.startTime);
    }
}
