import { illegalState } from "../../../../utils/throwErrors";

const jsonExtension = ".json";

export function joinJsonExtension(filePath: string): string {
    return `${filePath}${jsonExtension}`;
}

export function trimJsonExtension(filePath: string): string {
    return (
        trimSuffix(filePath, jsonExtension) ??
        illegalState(
            `failed to trim "${jsonExtension}" extension from file path: ${filePath}`
        )
    );
}

function trimSuffix(input: string, suffix: string): string | undefined {
    const suffixIndex = input.lastIndexOf(suffix);
    if (suffixIndex === -1 || suffixIndex + suffix.length !== input.length) {
        return undefined;
    }
    return input.substring(0, suffixIndex);
}
