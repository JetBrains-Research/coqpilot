import * as fs from "fs";
import * as path from "path";

import { exists } from "./pathUtils";

/**
 * Both input paths are expected to be resolved and absolute paths.
 */
export function checkIsInsideDirectory(
    inputPath: string,
    dirPath: string
): boolean {
    return inputPath.startsWith(dirPath);
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

export function deleteDirectory(dirPath: string) {
    fs.rmSync(dirPath, { recursive: true, force: true });
}

export function clearDirectory(dirPath: string) {
    deleteDirectory(dirPath);
    createDirectory(true, dirPath);
}

export function provideEmptyDirectoryOrThrow(
    dirPath: string,
    dirNameDescription: string,
    throwError: (errorMessage: string) => never
) {
    if (exists(dirPath)) {
        if (!checkDirectoryIsEmpty(dirPath)) {
            throwError(
                `${dirNameDescription} directory should be empty: "${dirPath}"`
            );
        }
    } else {
        createDirectory(true, dirPath);
    }
}
