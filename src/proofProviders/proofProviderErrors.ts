import { ErrorWithCause } from "../utils/errors/errorsUtils";

/**
 * Base class for the errors thrown by `ProofProvider`.
 */
export abstract class ProofProviderError extends ErrorWithCause {
    constructor(
        message: string | undefined,
        cause: Error | undefined = undefined
    ) {
        super(message, cause);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "ProofProviderError";
    }
}

/**
 * Represents the failure of the generation request caused by invalid parameters
 * configured by the user or the plugin.
 */
export class ConfigurationError extends ProofProviderError {
    constructor(message: string) {
        super(message);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "ConfigurationError";
    }
}

/**
 * Represents the failure of the generation request caused by inability
 * to reach a remote proofProvider or a remote resource.
 *
 * This error is not of `GenerationFailedError` type, because the actual proof-generation process
 * has not yet trully started and the problems are most likely on the user side.
 */
export class RemoteConnectionError extends ProofProviderError {
    constructor(message: string) {
        super(message);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "RemoteConnectionError";
    }
}

/**
 * Represents the failure of the actual proof-generation process,
 * i.e. after all parameters validation has been performed.
 */
export class GenerationFailedError extends ProofProviderError {
    constructor(readonly cause: Error) {
        super(undefined, cause);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "GenerationFailedError";
    }
}
