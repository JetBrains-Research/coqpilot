import * as fs from "fs";

export const defaultEncoding = "utf-8";

export function writeToFile<T>(
    text: string,
    filePath: string,
    onError: (e: any) => T
): T | undefined {
    try {
        fs.writeFileSync(filePath, text, defaultEncoding);
        return undefined;
    } catch (e) {
        return onError(e);
    }
}
