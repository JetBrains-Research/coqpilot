import { ProofGoal } from "../../../../coqLsp/coqLspTypes";

export type SerializedGoal = string; // TODO: maybe develop proper serialized typing

export function serializeGoal(goal: ProofGoal): SerializedGoal {
    return JSON.stringify(goal);
}

export function deserializeGoal(serializedGoal: SerializedGoal): ProofGoal {
    return JSON.parse(serializedGoal) as ProofGoal;
}
