import { TargetType } from "../structures/benchmarkingCore/completionGenerationTask";

export function getTargetTypeName(targetType: TargetType): string {
    switch (targetType) {
        case TargetType.ADMIT:
            return "complete hole";
        case TargetType.PROVE_THEOREM:
            return "prove theorem";
    }
}

export function prependWithZeros(n: number, maxN: number): string {
    const maxDigitsNumber = maxN.toString().length;
    const zerosToPrependNumber = maxDigitsNumber - n.toString().length;
    return `${"0".repeat(zerosToPrependNumber)}${n}`;
}
