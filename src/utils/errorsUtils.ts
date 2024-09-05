import { stringifyAnyValue } from "./printers";

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

export function asErrorOrRethrow(e: any): Error {
    if (!(e instanceof Error)) {
        throw e;
    }
    return e;
}

export function asErrorOrUndefined(e: any): Error | undefined {
    return e instanceof Error ? e : undefined;
}

export function buildErrorCompleteLog(e: any): string {
    if (!(e instanceof Error)) {
        return stringifyAnyValue(e);
    }
    return e.stack ?? `${e.name}: ${e.message}`;
}

export function getErrorMessage(e: any): string {
    if (!(e instanceof Error)) {
        return stringifyAnyValue(e);
    }
    return e.message;
}
