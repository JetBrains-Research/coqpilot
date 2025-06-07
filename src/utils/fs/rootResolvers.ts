import * as path from "path";

import { isAbsolutePath, joinPaths, resolveAsAbsolutePath } from "./pathUtils";

export function getRootDir(): string {
    const relativeRoot = path.join(__dirname, "/../../../");
    return path.resolve(relativeRoot);
}

export function getDatasetDir(): string {
    return path.join(getRootDir(), "dataset");
}

export function resolveAsAbsoluteOrRootRelativePath(filePath: string): string {
    if (isAbsolutePath(filePath)) {
        return filePath;
    }
    return resolveAsAbsolutePath(joinPaths(getRootDir(), filePath));
}
