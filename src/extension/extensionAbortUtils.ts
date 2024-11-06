export class CompletionAbortError extends Error {
    private static readonly abortMessage =
        "User has triggered a session abort: Stopping all completions";

    constructor() {
        super(CompletionAbortError.abortMessage);
        this.name = "CompletionAbortError";
    }
}

export function throwOnAbort(abortSignal?: AbortSignal) {
    if (abortSignal?.aborted) {
        throw abortSignal.reason;
    }
}
