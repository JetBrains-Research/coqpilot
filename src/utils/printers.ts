import { illegalState } from "./throwErrors";

export function stringifyAnyValue(
    value: any,
    space: JsonSpacing = JsonSpacing.UNFORMATTED
): string {
    const valueAsString = toJsonString(value, space);
    if (typeof value === "number") {
        return valueAsString;
    }
    return `"${valueAsString}"`;
}

export function stringifyDefinedValue(
    value: any,
    space: JsonSpacing = JsonSpacing.UNFORMATTED
): string {
    if (value === undefined) {
        illegalState(`value to stringify is not defined`);
    }
    return stringifyAnyValue(value, space);
}

export function toFormattedJsonString(object: any): string {
    return toJsonString(object, JsonSpacing.DEFAULT_FORMATTED);
}

export function toUnformattedJsonString(object: any): string {
    return toJsonString(object, JsonSpacing.UNFORMATTED);
}

export enum JsonSpacing {
    UNFORMATTED = 0,
    DEFAULT_FORMATTED = 2,
    WIDELY_FORMATTED = 4,
}

export function toJsonString(object: any, space: JsonSpacing): string {
    return JSON.stringify(object, null, space);
}
