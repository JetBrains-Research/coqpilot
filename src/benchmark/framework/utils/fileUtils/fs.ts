import * as fs from "fs";
import * as path from "path";

import { illegalState } from "../../../../utils/throwErrors";

export function getRootDir(): string {
    const relativeRoot = path.join(__dirname, "/../../../../../");
    return path.resolve(relativeRoot);
}

export function getDatasetDir(): string {
    return path.join(getRootDir(), "dataset");
}

export const defaultEncoding = "utf-8";

export function readFile<T>(
    filePath: string,
    onError: (error: Error) => T
): string | T {
    try {
        return fs.readFileSync(filePath, defaultEncoding);
    } catch (e) {
        return onError(e as Error);
    }
}

export function writeToFile<T>(
    text: string,
    filePath: string,
    onError: (error: Error) => T,
    createParentDirectories: boolean = false
): T | undefined {
    try {
        if (createParentDirectories) {
            createDirectory(false, getDirectoryPath(filePath));
        }
        fs.writeFileSync(filePath, text, defaultEncoding);
        return undefined;
    } catch (e) {
        return onError(e as Error);
    }
}

export function appendToFile<T>(
    text: string,
    filePath: string,
    onError: (e: any) => T
): T | undefined {
    try {
        fs.appendFileSync(filePath, text, defaultEncoding);
        return undefined;
    } catch (e) {
        return onError(e);
    }
}

export function clearFile(filePath: string) {
    fs.writeFileSync(filePath, "");
}

export function exists(inputPath: string): boolean {
    return fs.existsSync(inputPath);
}

export function joinPaths(parentDirPath: string, ...paths: string[]): string {
    return path.join(parentDirPath, ...paths);
}

export function isAbsolutePath(inputPath: string): boolean {
    return path.isAbsolute(inputPath);
}

export function resolveAsAbsolutePath(inputPath: string): string {
    return path.resolve(inputPath);
}

export function relativizeAbsolutePaths(parentPath: string, childPath: string) {
    return path.relative(parentPath, childPath);
}

export function getLastName(inputPath: string): string {
    return path.parse(inputPath).name;
}

export function getDirectoryPath(inputPath: string): string {
    return path.dirname(inputPath);
}

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

export type FileCreationModeOnExisting = "throw" | "clear" | "return";

export function createFileWithParentDirectories(
    mode: FileCreationModeOnExisting,
    filePath: string
) {
    if (fs.existsSync(filePath)) {
        switch (mode) {
            case "throw":
                illegalState(`failed to create ${filePath}: it already exists`);
            case "clear":
                clearFile(filePath);
                return;
            case "return":
                return;
        }
    }
    const parentDirPath = path.dirname(filePath);
    createDirectory(false, parentDirPath);
    clearFile(filePath);
}

export function getPathStats(inputPath: string): fs.Stats {
    return fs.lstatSync(inputPath);
}

export function isDirectory(inputPath: string): boolean {
    return getPathStats(inputPath).isDirectory();
}

export function isFile(inputPath: string): boolean {
    return getPathStats(inputPath).isFile();
}

export function isCoqSourceFile(inputPath: string): boolean {
    return (
        isFile(inputPath) &&
        path.extname(inputPath) === ".v" &&
        !inputPath.endsWith("_cp_aux.v")
    );
}

export function isJsonFile(inputPath: string): boolean {
    return isFile(inputPath) && path.extname(inputPath) === ".json";
}

/**
 * @param dirPath resolved absolute directory path.
 * @param depth determines the recursion depth of subdirectories traverse. `undefined` (the default value) corresponds to the unlimited depth; `0` correpsonds to listing the files located in the `dirPath` only.
 * @returns resolved absolute paths for the files inside `dirPath`.
 */
export function listCoqSourceFiles(
    dirPath: string,
    depth: number | undefined = undefined
): string[] {
    return listFiles(dirPath, depth, (filePath) => isCoqSourceFile(filePath));
}

/**
 * @param dirPath resolved absolute directory path.
 * @param depth determines the recursion depth of subdirectories traverse. `undefined` (the default value) corresponds to the unlimited depth; `0` correpsonds to listing the files located in the `dirPath` only.
 * @returns resolved absolute paths for the files inside `dirPath`.
 */
export function listJsonFiles(
    dirPath: string,
    depth: number | undefined = undefined
): string[] {
    return listFiles(dirPath, depth, (filePath) => isJsonFile(filePath));
}

/**
 * @param dirPath resolved absolute directory path.
 * @param depth determines the recursion depth of subdirectories traverse. `undefined` corresponds to the unlimited depth; `0` correpsonds to listing the files located in the `dirPath` only.
 * @param predicate filters the listed files (only ones with `true` value are returned).
 * @returns resolved absolute paths for the files inside `dirPath`.
 */
function listFiles(
    dirPath: string,
    depth: number | undefined,
    predicate: (filePath: string) => boolean
): string[] {
    if (depth !== undefined && depth < 0) {
        illegalState(`Files listing depth should be non-negative: ${depth}`);
    }
    let resultFilePaths: string[] = [];

    function traverseDirectory(
        curDirPath: string,
        depthLeft: number | undefined
    ) {
        fs.readdirSync(curDirPath).forEach((child) => {
            const childPath = path.join(curDirPath, child);
            if (isDirectory(childPath)) {
                if (depthLeft === undefined || depthLeft > 0) {
                    traverseDirectory(
                        childPath,
                        depthLeft === undefined ? undefined : depthLeft - 1
                    );
                }
            } else if (predicate(childPath)) {
                resultFilePaths.push(childPath);
            }
        });
    }

    traverseDirectory(dirPath, depth);
    return resultFilePaths;
}
