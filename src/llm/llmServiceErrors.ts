import { UserModelParams } from "./userModelParams";

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
 * Should be thrown iff `UserModelParams` could not be resolved.
 */
export class ParametersResolutionError extends LLMServiceError {
    constructor(cause: string, params: UserModelParams) {
        super(
            `user model parameters cannot be resolved: ${cause}, \`${params}\``
        );
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
    constructor(readonly cause: Error) {
        super("", cause);
    }
}
