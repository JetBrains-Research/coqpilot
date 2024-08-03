const jsonExtension = ".json";

export function joinJsonExtension(filePath: string): string {
    return `${filePath}${jsonExtension}`;
}

export function trimJsonExtension(filePath: string): string {
    const trimmedPath = trimSuffix(filePath, jsonExtension);
    if (trimmedPath === undefined) {
        throw Error(
            `Failed to trim "${jsonExtension}" extension from file path: ${filePath}`
        );
    }
    return trimmedPath;
}

function trimSuffix(input: string, suffix: string): string | undefined {
    const suffixIndex = input.lastIndexOf(suffix);
    if (suffixIndex === -1 || suffixIndex + suffix.length !== input.length) {
        return undefined;
    }
    return input.substring(0, suffixIndex);
}
