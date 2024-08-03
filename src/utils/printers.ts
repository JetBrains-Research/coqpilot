export function stringifyAnyValue(
    value: any,
    space: number | undefined = undefined
): string {
    const valueAsString = toJsonString(value, space);
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

export function toJsonString(
    object: any,
    space: number | undefined = undefined
): string {
    return JSON.stringify(object, null, space);
}
