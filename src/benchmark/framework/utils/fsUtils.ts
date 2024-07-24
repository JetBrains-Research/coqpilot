import * as fs from "fs";
import * as path from "path";

export function getRootDir(): string {
    const relativeRoot = path.join(__dirname, "/../../../../");
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
    onError: (error: Error) => T
): T | undefined {
    try {
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

export type FileCreationModeOnExisting = "throw" | "clear" | "return";

export function createFileWithParentDirectories(
    mode: FileCreationModeOnExisting,
    filePath: string
) {
    if (fs.existsSync(filePath)) {
        switch (mode) {
            case "throw":
                throw Error(`failed to create ${filePath}: it already exists`);
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

/**
 * @param dirPath resolved absolute directory path.
 * @returns resolved absolute paths for the files inside `dirPath`.
 */
export function listCoqSourceFiles(dirPath: string): string[] {
    let sourceFilePaths: string[] = [];
    function traverseDirectory(curDirPath: string) {
        fs.readdirSync(curDirPath).forEach((child) => {
            const childPath = path.join(curDirPath, child);
            if (isDirectory(childPath)) {
                traverseDirectory(childPath);
            } else if (isCoqSourceFile(childPath)) {
                sourceFilePaths.push(childPath);
            }
        });
    }
    traverseDirectory(dirPath);
    return sourceFilePaths;
}
