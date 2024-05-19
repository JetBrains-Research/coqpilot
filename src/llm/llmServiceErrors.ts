/**
 * Base class for the errors thrown by `LLMService`.
 */
export abstract class LLMServiceError extends Error {
    constructor(
        message: string = "",
        readonly cause: Error | undefined = undefined
    ) {
        let errorMessage = message;
        if (cause !== undefined) {
            const causeMessage = `cause: [${cause.name}] "${cause.message}"`;
            errorMessage =
                message === "" ? causeMessage : `${message}, ${causeMessage}`;
        }
        super(errorMessage);
    }
}

/**
 * Represents the failure of the generation request caused by invalid parameters
 * configured by the user or the plugin.
 */
export class ConfigurationError extends LLMServiceError {
    constructor(message: string) {
        super(message);
    }
}

/**
 * Represents the failure of the generation request caused by inability
 * to reach a remote service or a remote resource.
 *
 * This error is not of `GenerationFailedError` type, because the actual proof-generation process
 * has not yet trully started and the problems are most likely on the user side.
 */
export class RemoteConnectionError extends LLMServiceError {
    constructor(message: string) {
        super(message);
    }
}

/**
 * Represents the failure of the actual proof-generation process,
 * i.e. after all parameters validation has been performed.
 */
export class GenerationFailedError extends LLMServiceError {
    constructor(readonly cause: Error) {
        super("", cause);
    }
}
