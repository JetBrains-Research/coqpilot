import * as fs from "fs";
import * as path from "path";

import { wrapNonError } from "../errors/errorsUtils";
import { illegalState } from "../errors/throwErrors";

import { createDirectory } from "./directoryUtils";
import { isDirectory } from "./fileTypeCheckers";
import { getDirectoryPath, joinPaths, parsePath } from "./pathUtils";
import { getPathStats } from "./stats";

export const defaultEncoding = "utf-8";

export function readFile<T>(
    filePath: string,
    onError: (error: Error) => T
): string | T {
    try {
        return fs.readFileSync(filePath, defaultEncoding);
    } catch (e) {
        return handleThrownObject(e, onError);
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
        return handleThrownObject(e, onError);
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
        return handleThrownObject(e, onError);
    }
}

function handleThrownObject<T>(e: any, onError: (e: any) => T): T {
    if (e instanceof Error) {
        return onError(e);
    }
    return onError(
        wrapNonError(e, "non-`Error` object is thrown inside `writeToFile`")
    );
}

export function clearFile(filePath: string) {
    fs.writeFileSync(filePath, "");
}

export function deleteFile(filePath: string) {
    fs.rmSync(filePath, { force: true });
}

export function copyFile(
    sourceFilePath: string,
    destPath: string,
    throwOnExisting: boolean
): string {
    // TODO: known bug, `isDirectory` fails on non-existing path
    let destFilePath = isDirectory(destPath)
        ? joinPaths(destPath, parsePath(sourceFilePath).base)
        : destPath;
    fs.copyFileSync(
        sourceFilePath,
        destFilePath,
        throwOnExisting ? fs.constants.COPYFILE_EXCL : undefined
    );
    return destFilePath;
}

export function chmodFile(filePath: string, mode: fs.Mode) {
    fs.chmodSync(filePath, mode);
}

export function makeFileExecutable(filePath: string) {
    const currentMode = getPathStats(filePath).mode;
    const newMode = currentMode | 0o111;
    chmodFile(filePath, newMode);
}

export type FileCreationModeOnExisting = "throw" | "clear" | "return";

export function createFileWithParentDirectories(
    mode: FileCreationModeOnExisting,
    filePath: string
): string {
    if (fs.existsSync(filePath)) {
        switch (mode) {
            case "throw":
                illegalState(`failed to create ${filePath}: it already exists`);
            case "clear":
                clearFile(filePath);
                return filePath;
            case "return":
                return filePath;
        }
    }
    const parentDirPath = path.dirname(filePath);
    createDirectory(false, parentDirPath);
    clearFile(filePath);
    return filePath;
}
