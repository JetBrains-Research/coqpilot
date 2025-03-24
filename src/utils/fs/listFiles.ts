import * as fs from "fs";
import * as path from "path";

import { illegalState } from "../throwErrors";

import { isCoqSourceFile, isDirectory, isJsonFile } from "./fileTypeCheckers";

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
