export abstract class ErrorWithCause extends Error {
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
