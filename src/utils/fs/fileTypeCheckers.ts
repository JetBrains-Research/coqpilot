import * as fs from "fs";

import { AUX_FILE_SUBSTRING } from "../../llm/llmServices/utils/auxFileManager";

import { getExtensionName } from "./pathUtils";

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
        getExtensionName(inputPath) === ".v" &&
        !inputPath.includes(AUX_FILE_SUBSTRING)
    );
}

export function isJsonFile(inputPath: string): boolean {
    return isFile(inputPath) && getExtensionName(inputPath) === ".json";
}
