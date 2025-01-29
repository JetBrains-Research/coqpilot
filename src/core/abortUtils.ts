export class CompletionAbortError extends Error {
    private static readonly abortMessage =
        "Session abort has been triggered: stopping all completions";

    constructor() {
        super(CompletionAbortError.abortMessage);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "CompletionAbortError";
    }
}

export function throwOnAbort(abortSignal?: AbortSignal) {
    if (abortSignal?.aborted) {
        throw abortSignal.reason;
    }
}
