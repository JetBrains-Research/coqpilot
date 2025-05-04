import * as path from "path";

import { relativizeAbsolutePaths } from "../../utils/fs/pathUtils";
import { createTmpDirectory } from "../../utils/fs/tmpFs";

export function getRootDir(): string {
    const relativeRoot = path.join(__dirname, "/../../..");
    return path.resolve(relativeRoot);
}

export function getResourcesDir(): string {
    return path.join(getRootDir(), "src", "test", "resources");
}

export function resolveResourcesDir(
    resourcePath: string[],
    projectRootPath?: string[]
): [string, string] {
    const filePath = path.join(getResourcesDir(), ...resourcePath);
    const rootDir = path.join(getResourcesDir(), ...(projectRootPath ?? []));
    return [filePath, rootDir];
}

export function createRelativeTmpDir(): string {
    return relativizeAbsolutePaths(getRootDir(), createTmpDirectory());
}
