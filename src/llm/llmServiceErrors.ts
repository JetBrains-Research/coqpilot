/**
 * Base class for the errors thrown by `LLMService`.
 */
export abstract class LLMServiceError extends Error {
    constructor(
        message: string = "",
        public readonly cause: Error | undefined = undefined
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
 * Represents the failure of the actual proof-generation process,
 * i.e. after all parameters validation has been performed.
 */
export class GenerationFailedError extends LLMServiceError {
    constructor(cause: Error) {
        super("", cause);
    }
}