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

/**
 * Modifies and returns `totalTime`.
 */
export function addToTotalTime(
    totalTime: CompletionGenerationTime,
    otherTime: CompletionGenerationTime
): CompletionGenerationTime {
    totalTime.proofsGenerationMillis += otherTime.proofsGenerationMillis;
    totalTime.proofsValidationMillis =
        (totalTime.proofsValidationMillis ?? 0) +
        (otherTime.proofsValidationMillis ?? 0);
    totalTime.totalMillis += otherTime.totalMillis;
    return totalTime;
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
