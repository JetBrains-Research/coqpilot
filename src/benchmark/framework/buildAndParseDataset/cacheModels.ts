import { JSONSchemaType } from "ajv";

import {
    SerializedTheorem,
    serializedTheoremSchema,
} from "../structures/theoremData";
import {
    SerializedCodeElementRange,
    serializedCodeElementRangeSchema,
} from "../structures/utilStructures";

export namespace DatasetCacheModels {
    export interface CachedCoqFile {
        /**
         * All theorems that were successfully parsed from the file.
         * Ones that don't end with `Qed.` are also included.
         */
        allFileTheorems: CachedTheoremsByNames;

        fileLines: string[];
        fileVersion: number;
        filePathRelativeToWorkspace: string;
    }

    export type CachedTheoremsByNames = {
        [key: string]: CachedTheorem;
    };

    export interface CachedTheorem {
        theorem: SerializedTheorem;
        proofTarget: CachedTarget;
        admitTargets: CachedTarget[];
    }

    export interface CachedTarget {
        goalToProve: ParsedGoal;
        positionRange: SerializedCodeElementRange;
    }

    export type ParsedGoal = string;

    export const cachedTargetSchema: JSONSchemaType<CachedTarget> = {
        type: "object",
        properties: {
            goalToProve: {
                type: "string",
            },
            positionRange: serializedCodeElementRangeSchema,
        },
        required: ["goalToProve", "positionRange"],
        additionalProperties: false,
    };

    export const cachedTheoremSchema: JSONSchemaType<CachedTheorem> = {
        type: "object",
        properties: {
            theorem: serializedTheoremSchema,
            proofTarget: cachedTargetSchema,
            admitTargets: {
                type: "array",
                items: cachedTargetSchema,
            },
        },
        required: ["theorem", "proofTarget", "admitTargets"],
        additionalProperties: false,
    };

    export const cachedTheoremsByNamesSchema: JSONSchemaType<CachedTheoremsByNames> =
        {
            type: "object",
            patternProperties: {
                // eslint-disable-next-line @typescript-eslint/naming-convention
                "^.*$": cachedTheoremSchema,
            },
            required: [],
            additionalProperties: false,
        };

    export const cachedCoqFileSchema: JSONSchemaType<CachedCoqFile> = {
        type: "object",
        properties: {
            allFileTheorems: cachedTheoremsByNamesSchema,
            fileLines: {
                type: "array",
                items: {
                    type: "string",
                },
            },
            fileVersion: {
                type: "number",
            },
            filePathRelativeToWorkspace: {
                type: "string",
            },
        },
        required: [
            "allFileTheorems",
            "fileLines",
            "fileVersion",
            "filePathRelativeToWorkspace",
        ],
        additionalProperties: false,
    };
}
