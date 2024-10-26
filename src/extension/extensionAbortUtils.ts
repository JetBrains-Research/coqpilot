export class CompletionAbortError extends Error {
    static readonly abortMessage =
        "User has triggered a sesion abort: Stopping all completions";

    constructor() {
        super(CompletionAbortError.abortMessage);
    }
}

export function throwOnAbort(abortSignal: AbortSignal) {
    if (abortSignal.aborted) {
        throw abortSignal.reason;
    }
}