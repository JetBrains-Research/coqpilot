import * as fs from "fs";
import * as path from "path";

export function joinPaths(parentDirPath: string, ...paths: string[]): string {
    return path.join(parentDirPath, ...paths);
}

export function isAbsolutePath(inputPath: string): boolean {
    return path.isAbsolute(inputPath);
}

export function resolveAsAbsolutePath(inputPath: string): string {
    return path.resolve(inputPath);
}

export function resolvePossiblyRelativeAsAbsolutePath(
    inputPath: string,
    parentDirPath: string
): string {
    if (isAbsolutePath(inputPath)) {
        return resolveAsAbsolutePath(inputPath);
    }
    return resolveAsAbsolutePath(joinPaths(parentDirPath, inputPath));
}

export function relativizeAbsolutePaths(parentPath: string, childPath: string) {
    return path.relative(parentPath, childPath);
}

export function parsePath(inputPath: string): path.ParsedPath {
    return path.parse(inputPath);
}

export function getLastName(inputPath: string): string {
    return parsePath(inputPath).base;
}

export function getLastNameWithoutExtension(inputPath: string): string {
    return parsePath(inputPath).name;
}

export function getExtensionName(inputPath: string): string {
    return path.extname(inputPath);
}

export function getDirectoryPath(inputPath: string): string {
    return path.dirname(inputPath);
}

export function exists(inputPath: string): boolean {
    return fs.existsSync(inputPath);
}
