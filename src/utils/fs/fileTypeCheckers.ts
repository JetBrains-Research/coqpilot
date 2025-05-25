import { AUX_FILE_SUBSTRING } from "../../proofProviders/impl/utils/auxFileManager";

import { getExtensionName } from "./pathUtils";
import { getThisPathStats } from "./stats";

export function isDirectory(inputPath: string): boolean {
    return getThisPathStats(inputPath).isDirectory();
}

export function isFile(inputPath: string): boolean {
    return getThisPathStats(inputPath).isFile();
}

export function isCoqSourceFile(inputPath: string): boolean {
    return (
        isFile(inputPath) &&
        getExtensionName(inputPath) === ".v" &&
        !inputPath.includes(AUX_FILE_SUBSTRING)
    );
}

export function isJsonFile(inputPath: string): boolean {
    return isFile(inputPath) && getExtensionName(inputPath) === ".json";
}
