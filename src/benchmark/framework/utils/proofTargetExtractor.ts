import { ProofStep, Theorem } from "../../../coqParser/parsedTypes";
import {
    SerializedProofStep,
    SerializedTheorem,
    TheoremData,
} from "../structures/theoremData";

export function extractTheoremFisrtProofStep(
    theorem: TheoremData | Theorem
): ProofStep {
    return theorem.proof!.proof_steps[1];
}

export function extractSerializedTheoremFisrtProofStep(
    serializedTheorem: SerializedTheorem
): SerializedProofStep {
    return serializedTheorem.proof!.proof_steps[1];
}
