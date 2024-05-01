import * as path from "path";

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
