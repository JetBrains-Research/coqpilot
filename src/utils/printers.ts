export function stringifyAnyValue(value: any): string {
    const valueAsString = JSON.stringify(value);
    if (typeof value === "number") {
        return valueAsString;
    }
    return `"${valueAsString}"`;
}

export function stringifyDefinedValue(value: any): string {
    if (value === undefined) {
        throw Error(`value to stringify is not defined`);
    }
    return stringifyAnyValue(value);
}
