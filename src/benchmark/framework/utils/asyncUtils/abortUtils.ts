import { stringifyAnyValue } from "../../../../utils/printers";

export class FailFastAbortError extends Error {
    static readonly abortMessage =
        "Aborting all tasks: at least one task has already failed (`failFast` strategy is enabled)";

    constructor() {
        super(FailFastAbortError.abortMessage);
    }
}

export function abortAsFailFast(abortController: AbortController) {
    abortController.abort(new FailFastAbortError());
}

export function throwOnAbort(abortSignal: AbortSignal) {
    if (abortSignal.aborted) {
        const reason = abortSignal.reason;
        if (!(reason instanceof FailFastAbortError)) {
            throw Error(
                `Abort invariant failed: \`abortSignal.reason\` ${stringifyAnyValue(reason)} is not of \`FailFastAbortError\` class`
            );
        }
        throw abortSignal.reason;
    }
}
