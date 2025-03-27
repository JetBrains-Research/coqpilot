import * as path from "path";

export function getRootDir(): string {
    const relativeRoot = path.join(__dirname, "/../../../");
    return path.resolve(relativeRoot);
}

export function getDatasetDir(): string {
    return path.join(getRootDir(), "dataset");
}
