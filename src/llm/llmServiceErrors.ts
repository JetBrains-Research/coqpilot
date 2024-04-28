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

export class GenerationFromChatFailedError extends LLMServiceError {
    constructor(cause: Error) {
        super("", cause);
    }
}

export class InvalidRequestError extends LLMServiceError {
    constructor(message: string) {
        super(message);
    }
}
