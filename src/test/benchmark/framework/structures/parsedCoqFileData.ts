import { JSONSchemaType } from "ajv";

import {
    SerializedTheorem,
    TheoremData,
    deserializeTheorem,
    serializeTheorem,
    serializedTheoremSchema,
} from "./theoremData";

export interface ParsedCoqFileData {
    /**
     * All theorems that were successfully parsed from the file.
     * Ones that don't end with `Qed.` are also included.
     */
    allFileTheorems: TheoremData[];

    fileLines: string[];
    fileVersion: number;
    filePath: string;
}

export interface SerializedParsedCoqFile {
    /**
     * All theorems that were successfully parsed from the file.
     * Ones that don't end with `Qed.` are also included.
     */
    allFileTheorems: SerializedTheorem[];

    fileLines: string[];
    fileVersion: number;
    filePath: string;
}

export const serializedParsedCoqFileSchema: JSONSchemaType<SerializedParsedCoqFile> =
    {
        type: "object",
        properties: {
            allFileTheorems: {
                type: "array",
                items: serializedTheoremSchema,
            },
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
        required: ["allFileTheorems", "fileLines", "fileVersion", "filePath"],
        additionalProperties: false,
    };

export function deserializeParsedCoqFile(
    serializedParsedCoqFile: SerializedParsedCoqFile
): ParsedCoqFileData {
    return {
        ...serializedParsedCoqFile,
        allFileTheorems: serializedParsedCoqFile.allFileTheorems.map(
            (serializedTheorem) =>
                new TheoremData(deserializeTheorem(serializedTheorem))
        ),
    };
}

export function serializeParsedCoqFile(
    parsedCoqFileData: ParsedCoqFileData
): SerializedParsedCoqFile {
    return {
        ...parsedCoqFileData,
        allFileTheorems: parsedCoqFileData.allFileTheorems.map((theoremData) =>
            serializeTheorem(theoremData.theorem)
        ),
    };
}
