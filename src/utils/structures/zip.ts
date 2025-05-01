import { invariantFailed } from "../errors/throwErrors";
import { stringifyAnyValue } from "../printers";

export function zip<T, V>(ts: T[], vs: V[]): [T, V][] {
    if (ts.length !== vs.length) {
        invariantFailed(
            "Zip function",
            "arrays should be of the same length, ",
            `but got ${stringifyAnyValue(ts)} and ${stringifyAnyValue(vs)}`
        );
    }
    return ts.map((t, i) => [t, vs[i]]);
}
