import { stringifyAnyValue } from "../../../../utils/printers";
import { invariantFailed } from "../../../../utils/throwErrors";

export class FailFastAbortError extends Error {
    static readonly abortMessage =
        "Aborting all tasks: at least one task has already failed (`failFast` strategy is enabled)";

    constructor() {
        super(FailFastAbortError.abortMessage);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "FailFastAbortError";
    }
}

export function abortAsFailFast(abortController: AbortController) {
    abortController.abort(new FailFastAbortError());
}

export function throwOnAbort(abortSignal: AbortSignal) {
    if (abortSignal.aborted) {
        const reason = abortSignal.reason;
        if (!(reason instanceof FailFastAbortError)) {
            invariantFailed(
                "Abort",
                `\`abortSignal.reason\` ${stringifyAnyValue(reason)} is not of \`FailFastAbortError\` class`
            );
        }
        throw abortSignal.reason;
    }
}
