import { JSONSchemaType } from "ajv";

import { ProofCheckResult } from "../../../../../../core/coqProofChecker";

import { SerializedUri } from "../../../../structures/common/serializedUri";

export namespace CheckProofsInternalSignature {
    export const subprocessName = "Check generated proofs";

    export interface Args {
        workspaceRootPath: string | undefined;
        serializedFileUri: SerializedUri;
        documentVersion: number;
        positionToCheckAt: Position;
        preparedProofs: string[];
    }

    export interface Position {
        line: number;
        character: number;
    }

    export type Result = SuccessResult | FailureResult;

    export interface SuccessResult {
        checkedProofs: ProofCheckResult[];
        effectiveElapsedMillis: number;
    }

    export type FailureType = "COQ_LSP_TIMEOUT" | "COQ_PROOF_CHECKER_ERROR";

    export interface FailureResult {
        failureType: FailureType;
        causeMessage: string;
    }

    export function isSuccess(result: Result): result is SuccessResult {
        return "proofCheckResults" in result;
    }

    export function isFailure(result: Result): result is FailureResult {
        return "failureType" in result;
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
            serializedFileUri: {
                type: "string",
            },
            documentVersion: {
                type: "number",
            },
            positionToCheckAt: positionSchema,
            preparedProofs: {
                type: "array",
                items: {
                    type: "string",
                },
            },
        },
        required: [
            "serializedFileUri",
            "documentVersion",
            "positionToCheckAt",
            "preparedProofs",
        ],
        additionalProperties: false,
    };

    export const successResultSchema: JSONSchemaType<SuccessResult> = {
        type: "object",
        properties: {
            checkedProofs: {
                type: "array",
                items: proofCheckResultSchema,
            },
            effectiveElapsedMillis: {
                type: "number",
            },
        },
        required: ["checkedProofs", "effectiveElapsedMillis"],
        additionalProperties: false,
    };

    export const failureResultSchema: JSONSchemaType<FailureResult> = {
        type: "object",
        properties: {
            failureType: {
                type: "string",
                enum: ["COQ_LSP_TIMEOUT", "COQ_PROOF_CHECKER_ERROR"],
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
    };
}
