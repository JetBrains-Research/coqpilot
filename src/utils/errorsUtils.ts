import { stringifyAnyValue } from "./printers";
import { IllegalStateError } from "./throwErrors";

export function asErrorOrRethrow(e: any): Error {
    return ifErrorInstanceOrElse(
        e,
        () => e,
        () => {
            throw e;
        }
    );
}

export function asErrorOrRethrowWrapped(e: any, description: string): Error {
    return ifErrorInstanceOrElse(
        e,
        () => e,
        () => {
            throw wrapNonError(e, description);
        }
    );
}

export function wrapNonError(e: any, description: string): Error {
    return Error(`${description}: ${stringifyAnyValue(e)}`);
}

export function wrapAsIllegalState(e: any, description: string): Error {
    return new IllegalStateError(
        `${description}:\n${buildErrorCompleteLog(e)}`
    );
}

export function asErrorOrUndefined(e: any): Error | undefined {
    return e instanceof Error ? e : undefined;
}

export function getErrorMessage(e: any): string {
    return ifErrorInstanceOrElse(e, stringifyAnyValue, e.message);
}

export function buildErrorCompleteLog(e: any): string {
    return ifErrorInstanceOrElse(
        e,
        stringifyAnyValue,
        (e) => e.stack ?? errorToShortLog(e)
    );
}

export function buildErrorShortLog(e: any): string {
    return ifErrorInstanceOrElse(e, stringifyAnyValue, errorToShortLog);
}

function errorToShortLog(error: Error): string {
    return `${error.name}: ${error.message}`;
}

function ifErrorInstanceOrElse<T>(
    e: any,
    onError: (error: Error) => T,
    onElse: (e: any) => T
): T {
    if (e instanceof Error) {
        return onError(e);
    } else {
        return onElse(e);
    }
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
