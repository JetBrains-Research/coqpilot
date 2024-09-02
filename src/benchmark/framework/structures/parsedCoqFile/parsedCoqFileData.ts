import { JSONSchemaType } from "ajv";

import { SourceFileEnvironment } from "../../../../core/completionGenerationContext";

import { Theorem } from "../../../../coqParser/parsedTypes";
import { getDirectoryPath } from "../../utils/fsUtils";
import {
    fromMappedObject,
    mapValues,
    toMappedObject,
} from "../../utils/mapUtils";

import {
    SerializedTheorem,
    TheoremData,
    deserializeTheoremData,
    serializeTheoremData,
    serializedTheoremSchema,
} from "./theoremData";

export class ParsedCoqFileData {
    constructor(
        /**
         * All theorems that were successfully parsed from the file.
         * Ones that don't end with `Qed.` are also included.
         */
        readonly theoremsByNames: Map<string, TheoremData>,
        readonly fileLines: string[],
        readonly fileVersion: number,
        readonly filePath: string
    ) {}

    getOrderedFileTheorems(): Theorem[] {
        return Array.from(this.theoremsByNames.values())
            .sort(
                (theoremDataA, theoremDataB) =>
                    theoremDataA.fileTheoremsIndex -
                    theoremDataB.fileTheoremsIndex
            )
            .map((theoremData) => theoremData.sourceTheorem);
    }

    constructSourceFileEnvironment(): SourceFileEnvironment {
        return {
            fileTheorems: this.getOrderedFileTheorems().filter(
                (theorem) => theorem.proof && !theorem.proof.is_incomplete
            ),
            fileLines: this.fileLines,
            fileVersion: this.fileVersion,
            dirPath: getDirectoryPath(this.filePath),
        };
    }
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
    return new ParsedCoqFileData(
        mapValues(
            fromMappedObject(serializedParsedCoqFile.serializedTheoremsByNames),
            (_: string, serializedTheorem: SerializedTheorem) =>
                deserializeTheoremData(serializedTheorem)
        ),
        serializedParsedCoqFile.fileLines,
        serializedParsedCoqFile.fileVersion,
        serializedParsedCoqFile.filePath
    );
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
