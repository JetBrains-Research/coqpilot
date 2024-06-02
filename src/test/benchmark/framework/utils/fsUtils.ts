import * as fs from "fs";
import * as path from "path";

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

export function joinPaths(parentDirPath: string, ...paths: string[]): string {
    return path.join(parentDirPath, ...paths);
}

export function getLastName(filePath: string): string {
    return path.parse(filePath).name;
}

export function checkDirectoryIsEmpty(dirPath: string): boolean {
    return fs.readdirSync(dirPath).length === 0;
}

export function createDirectory(
    throwOnExisting: boolean,
    parentDirPath: string,
    ...subDirPaths: string[]
): string {
    const dirPath = path.join(parentDirPath, ...subDirPaths);
    if (!throwOnExisting && fs.existsSync(dirPath)) {
        return dirPath;
    }
    fs.mkdirSync(dirPath, { recursive: true });
    return dirPath;
}
