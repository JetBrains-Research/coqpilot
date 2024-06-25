export function stringifyAnyValue(
    value: any,
    space: number | undefined = undefined
): string {
    const valueAsString = JSON.stringify(value, null, space);
    if (typeof value === "number") {
        return valueAsString;
    }
    return `"${valueAsString}"`;
}

export function stringifyDefinedValue(
    value: any,
    space: number | undefined = undefined
): string {
    if (value === undefined) {
        throw Error(`value to stringify is not defined`);
    }
    return stringifyAnyValue(value, space);
}
