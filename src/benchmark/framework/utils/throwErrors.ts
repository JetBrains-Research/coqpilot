import { InvariantFailedError } from "../../../utils/throwErrors";
import { BenchmarkingLogger } from "../logging/benchmarkingLogger";

export function throwBenchmarkingError(...errorMessage: string[]): never {
    throw new BenchmarkingError(errorMessage.join(""));
}

/**
 * `BenchmarkingError` represents the expected error caused by
 *  the user or the environment during the benchmarking framework execution.
 */
export class BenchmarkingError extends Error {
    constructor(message: string) {
        super(message);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "BenchmarkingError";
    }
}

export function benchmarkingInvariantFailed(
    logger: BenchmarkingLogger,
    ...errorMessage: string[]
): never {
    const joinedMessage = `Benchmarking invariant failed: ${errorMessage.join("")}`;
    logger.error(joinedMessage);
    throw new InvariantFailedError(joinedMessage);
}
