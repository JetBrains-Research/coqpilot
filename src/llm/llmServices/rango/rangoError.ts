import { buildErrorCompleteLog } from "../../../utils/errors/errorsUtils";
import { IllegalStateError } from "../../../utils/errors/throwErrors";

export class RangoError extends Error {
    constructor(
        message: string,
        readonly logsPath?: string
    ) {
        const completeMessage =
            logsPath === undefined
                ? message
                : `${message}. Logs are available at ${logsPath}.`;
        super(completeMessage);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "RangoError";
    }
}

export function throwRangoError(...message: string[]): never {
    throw new RangoError(message.join(""));
}

export function throwRangoErrorWithLogs(
    logsAvailableAtPath: string,
    ...message: string[]
): never {
    throw new RangoError(message.join(""), logsAvailableAtPath);
}

export function asRangoErrorOrIllegalState(e: any): Error {
    if (e instanceof RangoError) {
        return e;
    }
    return new IllegalStateError(
        `Rango got unexpected error: ${buildErrorCompleteLog(e)}`
    );
}
