import { JSONSchemaType } from "ajv";

import { ProofCheckResult } from "../../../../../core/coqProofChecker";

export namespace CheckProofsBySubprocessSignature {
    export const subprocessName = "Check generated proofs";

    export interface Args {
        workspaceRootPath: string | undefined;
        sourceFileDirPath: string;
        sourceFileContentPrefix: string[];
        prefixEndPosition: Position;
        preparedProofs: string[];
    }

    export interface Position {
        line: number;
        character: number;
    }

    export type Result = SuccessResult | FailureResult;

    export interface SuccessResult {
        proofCheckResults: ProofCheckResult[];
        proofsValidationMillis: number;
    }

    export type FailureType = "timeout" | "coq-proof-checker-error";

    export interface FailureResult {
        failureType: FailureType;
        causeMessage: string;
    }

    export const positionSchema: JSONSchemaType<Position> = {
        type: "object",
        properties: {
            line: {
                type: "number",
            },
            character: {
                type: "number",
            },
        },
        required: ["line", "character"],
        additionalProperties: false,
    };

    export const proofCheckResultSchema: JSONSchemaType<ProofCheckResult> = {
        type: "object",
        properties: {
            proof: {
                type: "string",
            },
            isValid: {
                type: "boolean",
            },
            diagnostic: {
                type: "string",
                nullable: true,
            },
        },
        required: ["proof", "isValid"],
        additionalProperties: false,
    };

    export const argsSchema: JSONSchemaType<Args> = {
        type: "object",
        properties: {
            workspaceRootPath: {
                type: "string",
                nullable: true,
            },
            sourceFileDirPath: {
                type: "string",
            },
            sourceFileContentPrefix: {
                type: "array",
                items: {
                    type: "string",
                },
            },
            prefixEndPosition: positionSchema,
            preparedProofs: {
                type: "array",
                items: {
                    type: "string",
                },
            },
        },
        required: [
            "sourceFileDirPath",
            "sourceFileContentPrefix",
            "prefixEndPosition",
            "preparedProofs",
        ],
        additionalProperties: false,
    };

    export const successResultSchema: JSONSchemaType<SuccessResult> = {
        type: "object",
        properties: {
            proofCheckResults: {
                type: "array",
                items: proofCheckResultSchema,
            },
            proofsValidationMillis: {
                type: "number",
            },
        },
        required: ["proofCheckResults", "proofsValidationMillis"],
        additionalProperties: false,
    };

    export const failureResultSchema: JSONSchemaType<FailureResult> = {
        type: "object",
        properties: {
            failureType: {
                type: "string",
                enum: ["timeout", "coq-proof-checker-error"],
            },
            causeMessage: {
                type: "string",
            },
        },
        required: ["failureType", "causeMessage"],
        additionalProperties: false,
    };

    export const resultSchema: JSONSchemaType<SuccessResult | FailureResult> = {
        type: "object",
        oneOf: [successResultSchema, failureResultSchema],
        additionalProperties: false,
    };
}
