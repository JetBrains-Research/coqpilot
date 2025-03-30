export function throwOnAbort(abortSignal?: AbortSignal) {
    if (abortSignal?.aborted) {
        throw abortSignal.reason;
    }
}
