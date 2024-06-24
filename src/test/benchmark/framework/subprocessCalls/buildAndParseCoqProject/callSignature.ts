import { JSONSchemaType } from "ajv";

import { Goal, PpString } from "../../../../../coqLsp/coqLspTypes";

import { TargetType } from "../../structures/completionGenerationTask";
import {
    ParsedCoqFileData,
    SerializedParsedCoqFile,
    serializedParsedCoqFileSchema,
} from "../../structures/parsedCoqFileData";
import {
    CodeElementRange,
    SerializedCodeElementRange,
    serializedCodeElementRangeSchema,
} from "../../structures/utilStructures";

export namespace BuildAndParseCoqProjectBySubprocessSignature {
    export const subprocessName = "Build and parse Coq project";

    export namespace CommonModels {
        // Note: must correspond to `TargetType` enum from outside
        export type TargetType = "ADMIT" | "PROVE_THEOREM";

        export const targetTypeSchema: JSONSchemaType<TargetType> = {
            type: "string",
            enum: ["TIMEOUT", "COQ_PROOF_CHECKER_ERROR"],
        };
    }

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
            sourceFilePathToTarget: FilePathToFileTarget;
        }

        export type FilePathToFileTarget = { [key: string]: FileTarget };

        export interface FileTarget {
            specificTheoremTargets: TheoremNameToTheoremTarget;
            allTheoremsTargetTypes: CommonModels.TargetType[];
        }

        export type TheoremNameToTheoremTarget = {
            [key: string]: TheoremTarget;
        };

        export interface TheoremTarget {
            targetTypes: CommonModels.TargetType[];
        }

        export const theoremTargetSchema: JSONSchemaType<TheoremTarget> = {
            type: "object",
            properties: {
                targetTypes: {
                    type: "array",
                    items: CommonModels.targetTypeSchema,
                },
            },
            required: ["targetTypes"],
            additionalProperties: false,
        };

        export const theoremNameToTheoremTargetSchema: JSONSchemaType<TheoremNameToTheoremTarget> =
            {
                type: "object",
                patternProperties: {
                    // eslint-disable-next-line @typescript-eslint/naming-convention
                    "^.*$": theoremTargetSchema,
                },
                required: [],
                additionalProperties: false,
            };

        export const fileTargetSchema: JSONSchemaType<FileTarget> = {
            type: "object",
            properties: {
                specificTheoremTargets: theoremNameToTheoremTargetSchema,
                allTheoremsTargetTypes: {
                    type: "array",
                    items: CommonModels.targetTypeSchema,
                },
            },
            required: ["specificTheoremTargets", "allTheoremsTargetTypes"],
            additionalProperties: false,
        };

        export const filePathToFileTargetSchema: JSONSchemaType<FilePathToFileTarget> =
            {
                type: "object",
                patternProperties: {
                    // eslint-disable-next-line @typescript-eslint/naming-convention
                    "^.*$": fileTargetSchema,
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
                sourceFilePathToTarget: filePathToFileTargetSchema,
            },
            required: ["sourceFilePathToTarget"],
            additionalProperties: false,
        };
    }

    export namespace ResultModels {
        export type Result = FilePathToParsedFileTarget;

        export type FilePathToParsedFileTarget = {
            [key: string]: ParsedFileTarget;
        };

        export interface ParsedFileTarget {
            serializedParsedFile: SerializedParsedCoqFile;
            extractedTaskTargets: TaskTarget[];
        }

        export type ParsedGoal = string; // TODO: maybe develop proper serialized typing

        export interface TaskTarget {
            targetGoalToProve: ParsedGoal;
            targetPositionRange: SerializedCodeElementRange;
            targetType: CommonModels.TargetType;
        }

        export const taskTargetSchema: JSONSchemaType<TaskTarget> = {
            type: "object",
            properties: {
                targetGoalToProve: {
                    type: "string",
                },
                targetPositionRange: serializedCodeElementRangeSchema,
                targetType: CommonModels.targetTypeSchema,
            },
            required: [
                "targetGoalToProve",
                "targetPositionRange",
                "targetType",
            ],
            additionalProperties: false,
        };

        export const parsedFileTargetSchema: JSONSchemaType<ParsedFileTarget> =
            {
                type: "object",
                properties: {
                    serializedParsedFile: serializedParsedCoqFileSchema,
                    extractedTaskTargets: {
                        type: "array",
                        items: taskTargetSchema,
                    },
                },
                required: ["serializedParsedFile", "extractedTaskTargets"],
                additionalProperties: false,
            };

        export const filePathToParsedFileTargetSchema: JSONSchemaType<FilePathToParsedFileTarget> =
            {
                type: "object",
                patternProperties: {
                    // eslint-disable-next-line @typescript-eslint/naming-convention
                    "^.*$": parsedFileTargetSchema,
                },
                required: [],
                additionalProperties: false,
            };

        export const resultSchema: JSONSchemaType<Result> =
            filePathToParsedFileTargetSchema;
    }

    export namespace UnpackedResultModels {
        export type UnpackedResult = FilePathToParsedFileTarget;

        export type FilePathToParsedFileTarget = Map<string, ParsedFileTarget>;

        export interface ParsedFileTarget {
            parsedFile: ParsedCoqFileData;
            extractedTaskTargets: TaskTarget[];
        }

        export interface TaskTarget {
            targetGoalToProve: Goal<PpString>;
            targetPositionRange: CodeElementRange;
            targetType: TargetType;
        }
    }
}
