import { JSONSchemaType } from "ajv";

import { TargetType } from "../../structures/completionGenerationTask";
import { TargetRequestType } from "../../structures/inputTargets";
import {
    SerializedParsedCoqFile,
    serializedParsedCoqFileSchema,
} from "../../structures/parsedCoqFileData";
import {
    SerializedCodeElementRange,
    serializedCodeElementRangeSchema,
} from "../../structures/utilStructures";

export namespace BuildAndParseCoqProjectBySubprocessSignature {
    export const subprocessName = "Build and parse Coq project";

    export namespace ArgsModels {
        export interface Args {
            /**
             * Workspace root path is expected be absolute resolved path inside `"dataset"` directory
             * or undefined for standalone source file inside `"dataset"` directory.
             */
            workspaceRootPath: string | undefined;

            /**
             * File paths are expected to be absolute resolved paths inside `worspaceRootPath` directory
             * (or inside `"dataset"` directory if workspace is undefined).
             */
            workspaceTargets: FilePathToFileTargets;
        }

        export type FilePathToFileTargets = { [key: string]: FileTarget[] };

        export interface FileTarget {
            requestType: TargetRequestType;
            /**
             * If `specificTheoremName` is undefined, this target means request on all file theorems.
             */
            specificTheoremName: string | undefined;
        }

        export const targetRequestTypeSchema: JSONSchemaType<TargetRequestType> =
            {
                type: "string",
                enum: Object.values(
                    TargetRequestType
                ) as readonly TargetRequestType[],
            };

        export const fileTargetSchema: JSONSchemaType<FileTarget> = {
            type: "object",
            properties: {
                requestType: targetRequestTypeSchema,
                specificTheoremName: {
                    type: "string",
                    nullable: true,
                },
            },
            required: ["requestType"],
            additionalProperties: false,
        };

        export const filePathToFileTargetsSchema: JSONSchemaType<FilePathToFileTargets> =
            {
                type: "object",
                patternProperties: {
                    // eslint-disable-next-line @typescript-eslint/naming-convention
                    "^.*$": {
                        type: "array",
                        items: fileTargetSchema,
                    },
                },
                required: [],
                additionalProperties: false,
            };

        export const argsSchema: JSONSchemaType<Args> = {
            type: "object",
            properties: {
                workspaceRootPath: {
                    type: "string",
                    nullable: true,
                },
                workspaceTargets: filePathToFileTargetsSchema,
            },
            required: ["workspaceTargets"],
            additionalProperties: false,
        };
    }

    export namespace ResultModels {
        export type Result = FilePathToFileResults;

        export type FilePathToFileResults = {
            [key: string]: ParsedFileResults;
        };

        export interface ParsedFileResults {
            serializedParsedFile: SerializedParsedCoqFile;
            parsedFileTargets: ParsedFileTarget[];
        }

        export interface ParsedFileTarget {
            theoremName: string;
            targetType: TargetType;
            goalToProve: ParsedGoal;
            positionRange: SerializedCodeElementRange;
        }

        export type ParsedGoal = string; // TODO: maybe develop proper serialized typing

        export const parsedFileTargetSchema: JSONSchemaType<ParsedFileTarget> =
            {
                type: "object",
                properties: {
                    theoremName: {
                        type: "string",
                    },
                    targetType: {
                        type: "string",
                        enum: Object.values(
                            TargetType
                        ) as readonly TargetType[],
                    },
                    goalToProve: {
                        type: "string",
                    },
                    positionRange: serializedCodeElementRangeSchema,
                },
                required: [
                    "theoremName",
                    "targetType",
                    "goalToProve",
                    "positionRange",
                ],
                additionalProperties: false,
            };

        export const parsedFileResultsSchema: JSONSchemaType<ParsedFileResults> =
            {
                type: "object",
                properties: {
                    serializedParsedFile: serializedParsedCoqFileSchema,
                    parsedFileTargets: {
                        type: "array",
                        items: parsedFileTargetSchema,
                    },
                },
                required: ["serializedParsedFile", "parsedFileTargets"],
                additionalProperties: false,
            };

        export const filePathToFileResultsSchema: JSONSchemaType<FilePathToFileResults> =
            {
                type: "object",
                patternProperties: {
                    // eslint-disable-next-line @typescript-eslint/naming-convention
                    "^.*$": parsedFileResultsSchema,
                },
                required: [],
                additionalProperties: false,
            };

        export const resultSchema: JSONSchemaType<Result> =
            filePathToFileResultsSchema;
    }
}
