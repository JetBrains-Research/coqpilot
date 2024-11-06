/* eslint-disable @typescript-eslint/naming-convention */
import { JSONSchemaType } from "ajv";

import {
    ProofStep,
    Theorem,
    TheoremProof,
    Vernacexpr,
} from "../../../../coqParser/parsedTypes";
import {
    SerializedGoal,
    deserializeGoal,
    serializeGoal,
} from "../../utils/coqUtils/goalParser";
import {
    SerializedCodeElementRange,
    deserializeCodeElementRange,
    serializeCodeElementRange,
    serializedCodeElementRangeSchema,
} from "../common/codeElementPositions";

export class TheoremData {
    constructor(
        readonly sourceTheorem: Theorem,
        readonly fileTheoremsIndex: number
    ) {}

    readonly name = this.sourceTheorem.name;
    readonly proof = this.sourceTheorem.proof;
}

export interface SerializedTheorem {
    name: string;
    statement_range: SerializedCodeElementRange;
    statement: string;
    proof: SerializedTheoremProof;
    initial_goal: SerializedGoal | undefined;
    fileTheoremsIndex: number;
}

export interface SerializedTheoremProof {
    proof_steps: SerializedProofStep[];
    end_pos: SerializedCodeElementRange;
    is_incomplete: boolean;
    holes: SerializedProofStep[];
}

export interface SerializedProofStep {
    text: string;
    vernac_type: string;
    range: SerializedCodeElementRange;
}

export const serializedProofStepSchema: JSONSchemaType<SerializedProofStep> = {
    type: "object",
    properties: {
        text: {
            type: "string",
        },
        vernac_type: {
            type: "string",
        },
        range: serializedCodeElementRangeSchema,
    },
    required: [],
    additionalProperties: false,
};

export const serializedTheoremProofSchema: JSONSchemaType<SerializedTheoremProof> =
    {
        type: "object",
        properties: {
            proof_steps: {
                type: "array",
                items: serializedProofStepSchema,
            },
            end_pos: serializedCodeElementRangeSchema,
            is_incomplete: {
                type: "boolean",
            },
            holes: {
                type: "array",
                items: serializedProofStepSchema,
            },
        },
        required: ["proof_steps", "end_pos", "is_incomplete", "holes"],
        additionalProperties: false,
    };

export const serializedTheoremSchema: JSONSchemaType<SerializedTheorem> = {
    type: "object",
    properties: {
        name: {
            type: "string",
        },
        statement_range: serializedCodeElementRangeSchema,
        statement: {
            type: "string",
        },
        proof: {
            type: "object",
            oneOf: [serializedTheoremProofSchema],
        },
        initial_goal: {
            type: "string",
            nullable: true,
        },
        fileTheoremsIndex: {
            type: "number",
        },
    },
    required: ["name", "statement_range", "statement", "fileTheoremsIndex"],
    additionalProperties: false,
};

export function deserializeTheoremData(
    serializedTheorem: SerializedTheorem
): TheoremData {
    const serializedTheoremProof = serializedTheorem.proof;
    const theoremProof = new TheoremProof(
        serializedTheoremProof.proof_steps.map(deserializeProofStep),
        deserializeCodeElementRange(serializedTheoremProof.end_pos),
        serializedTheoremProof.is_incomplete,
        serializedTheoremProof.holes.map(deserializeProofStep)
    );
    const serializedInitialGoal = serializedTheorem.initial_goal;
    const initialGoal =
        serializedInitialGoal === undefined
            ? null
            : deserializeGoal(serializedInitialGoal);
    return new TheoremData(
        new Theorem(
            serializedTheorem.name,
            deserializeCodeElementRange(serializedTheorem.statement_range),
            serializedTheorem.statement,
            theoremProof,
            initialGoal
        ),
        serializedTheorem.fileTheoremsIndex
    );
}

export function serializeTheoremData(
    theoremData: TheoremData
): SerializedTheorem {
    const theoremProof = theoremData.proof;
    const serializedTheoremProof = {
        proof_steps: theoremProof.proof_steps.map(serializeProofStep),
        end_pos: serializeCodeElementRange(theoremProof.end_pos),
        is_incomplete: theoremProof.is_incomplete,
        holes: theoremProof.holes.map(serializeProofStep),
    };
    const initialGoal = theoremData.sourceTheorem.initial_goal;
    const serializedInitialGoal =
        initialGoal === null ? undefined : serializeGoal(initialGoal);
    return {
        name: theoremData.name,
        statement_range: serializeCodeElementRange(
            theoremData.sourceTheorem.statement_range
        ),
        statement: theoremData.sourceTheorem.statement,
        proof: serializedTheoremProof,
        initial_goal: serializedInitialGoal,
        fileTheoremsIndex: theoremData.fileTheoremsIndex,
    };
}

function deserializeProofStep(
    serializedProofStep: SerializedProofStep
): ProofStep {
    return new ProofStep(
        serializedProofStep.text,
        Vernacexpr[serializedProofStep.vernac_type as keyof typeof Vernacexpr], // Note: assuming keys and values of `Vernacexpr` are the same
        deserializeCodeElementRange(serializedProofStep.range)
    );
}

function serializeProofStep(proofStep: ProofStep): SerializedProofStep {
    return {
        text: proofStep.text,
        vernac_type: proofStep.vernac_type,
        range: serializeCodeElementRange(proofStep.range),
    };
}
