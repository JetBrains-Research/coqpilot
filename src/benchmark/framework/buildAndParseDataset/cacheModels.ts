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

    /**
     * Although some of the proof/admit targets might not be saved as parsed ones
     * (their `goalToProve` will be `undefined`), the set of their potential locations is always complete.
     * In other words, `CachedTheorem` always provides the set of
     * all the available proof/admit targets the theorem has.
     */
    export interface CachedTheorem {
        theorem: SerializedTheorem;
        proofTarget: CachedTarget;
        admitTargets: CachedTarget[];
    }

    export interface CachedTarget {
        /**
         * `undefined` value means that this goal is not present in the cache.
         */
        goalToProve: ParsedGoal | undefined;
        positionRange: SerializedCodeElementRange;
    }

    export type ParsedGoal = string;

    export const cachedTargetSchema: JSONSchemaType<CachedTarget> = {
        type: "object",
        properties: {
            goalToProve: {
                type: "string",
                nullable: true,
            },
            positionRange: serializedCodeElementRangeSchema,
        },
        required: ["positionRange"],
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
