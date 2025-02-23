import { buildErrorShortLog } from "../../../../utils/errorsUtils";
import { stringifyAnyValue } from "../../../../utils/printers";
import { invariantFailed } from "../../../../utils/throwErrors";

export class AbortError extends Error {
    private static readonly abortMessage = "Aborting all tasks: ";

    constructor(cause: string) {
        super(`${AbortError.abortMessage}${cause}`);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "AbortError";
    }
}

export class FailFastAbortError extends AbortError {
    private static readonly abortCause =
        "at least one task has already failed (`failFast` strategy is enabled)";

    constructor() {
        super(FailFastAbortError.abortCause);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "FailFastAbortError";
    }
}

export class CriticalAbortError extends AbortError {
    static readonly abortCause = "critical error occurred";

    constructor(causingError: any) {
        super(
            `${CriticalAbortError.abortCause}\n${buildErrorShortLog(causingError)}`
        );
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "CriticalAbortError";
    }
}

export function abortAsFailFast(abortController: AbortController) {
    abortController.abort(new FailFastAbortError());
}

export function abortAsCriticalError(
    abortController: AbortController,
    causingError: any
) {
    abortController.abort(new CriticalAbortError(causingError));
}

export function throwOnAbort(abortSignal: AbortSignal) {
    if (abortSignal.aborted) {
        const reason = abortSignal.reason;
        if (!(reason instanceof AbortError)) {
            invariantFailed(
                "Abort",
                `\`abortSignal.reason\` ${stringifyAnyValue(reason)} is not of \`AbortError\` class`
            );
        }
        throw abortSignal.reason;
    }
}
