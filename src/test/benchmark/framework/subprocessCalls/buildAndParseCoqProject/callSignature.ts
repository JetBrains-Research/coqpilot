import { JSONSchemaType } from "ajv";

import {
    SerializedParsedCoqFile,
    serializedParsedCoqFileSchema,
} from "../../structures/parsedCoqFileData";

export namespace BuildAndParseCoqProjectBySubprocessSignature {
    export const subprocessName = "Build and parse Coq project";

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
        sourceFilesToParsePaths: string[];
    }

    export type Result = SerializedParsedCoqFile[];

    export const argsSchema: JSONSchemaType<Args> = {
        type: "object",
        properties: {
            workspaceRootPath: {
                type: "string",
                nullable: true,
            },
            sourceFilesToParsePaths: {
                type: "array",
                items: {
                    type: "string",
                },
            },
        },
        required: ["sourceFilesToParsePaths"],
        additionalProperties: false,
    };

    export const resultSchema: JSONSchemaType<Result> = {
        type: "array",
        items: serializedParsedCoqFileSchema,
    };
}
