import { JSONSchemaType } from "ajv";

import { fromMappedObject, mapValues, toMappedObject } from "../utils/mapUtils";

import {
    SerializedTheorem,
    TheoremData,
    deserializeTheoremData,
    serializeTheoremData,
    serializedTheoremSchema,
} from "./theoremData";

// TODO: make a class?
export interface ParsedCoqFileData {
    /**
     * All theorems that were successfully parsed from the file.
     * Ones that don't end with `Qed.` are also included.
     */
    theoremsByNames: Map<string, TheoremData>;

    fileLines: string[];
    fileVersion: number;
    filePath: string;
}

export interface SerializedParsedCoqFile {
    /**
     * All theorems that were successfully parsed from the file.
     * Ones that don't end with `Qed.` are also included.
     */
    serializedTheoremsByNames: SerializedTheoremsByNames;

    fileLines: string[];
    fileVersion: number;
    filePath: string;
}

export type SerializedTheoremsByNames = {
    [theoremName: string]: SerializedTheorem;
};

export const serializedTheoremsByNamesSchema: JSONSchemaType<SerializedTheoremsByNames> =
    {
        type: "object",
        patternProperties: {
            // eslint-disable-next-line @typescript-eslint/naming-convention
            "^.*$": serializedTheoremSchema,
        },
        required: [],
        additionalProperties: false,
    };

export const serializedParsedCoqFileSchema: JSONSchemaType<SerializedParsedCoqFile> =
    {
        type: "object",
        properties: {
            serializedTheoremsByNames: serializedTheoremsByNamesSchema,
            fileLines: {
                type: "array",
                items: {
                    type: "string",
                },
            },
            fileVersion: {
                type: "number",
            },
            filePath: {
                type: "string",
            },
        },
        required: [
            "serializedTheoremsByNames",
            "fileLines",
            "fileVersion",
            "filePath",
        ],
        additionalProperties: false,
    };

export function deserializeParsedCoqFile(
    serializedParsedCoqFile: SerializedParsedCoqFile
): ParsedCoqFileData {
    return {
        theoremsByNames: mapValues(
            fromMappedObject(serializedParsedCoqFile.serializedTheoremsByNames),
            (_: string, serializedTheorem: SerializedTheorem) =>
                deserializeTheoremData(serializedTheorem)
        ),
        fileLines: serializedParsedCoqFile.fileLines,
        fileVersion: serializedParsedCoqFile.fileVersion,
        filePath: serializedParsedCoqFile.filePath,
    };
}

export function serializeParsedCoqFile(
    parsedCoqFileData: ParsedCoqFileData
): SerializedParsedCoqFile {
    return {
        serializedTheoremsByNames: toMappedObject(
            mapValues(
                parsedCoqFileData.theoremsByNames,
                (_: string, theoremData: TheoremData) =>
                    serializeTheoremData(theoremData)
            )
        ),
        fileLines: parsedCoqFileData.fileLines,
        fileVersion: parsedCoqFileData.fileVersion,
        filePath: parsedCoqFileData.filePath,
    };
}
