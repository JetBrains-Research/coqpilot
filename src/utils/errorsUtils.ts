import { stringifyAnyValue } from "./printers";

export function asErrorOrRethrow(e: any): Error {
    if (!(e instanceof Error)) {
        throw e;
    }
    return e;
}

export function asErrorOrRethrowWrapped(e: any, description: string): Error {
    if (!(e instanceof Error)) {
        throw wrapNonError(e, description);
    }
    return e;
}

export function wrapNonError(e: any, description: string): Error {
    return Error(`${description}: ${stringifyAnyValue(e)}`);
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

export abstract class ErrorWithCause extends Error {
    constructor(
        message: string | undefined,
        readonly cause: Error | undefined = undefined
    ) {
        const causeMessage =
            cause === undefined ? "" : `[${cause.name}] "${cause.message}"`;
        const errorMessage =
            message === undefined
                ? causeMessage
                : cause === undefined
                  ? message
                  : `${message}, cause: ${causeMessage}`;
        super(errorMessage);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "ErrorWithCause";
    }
}
