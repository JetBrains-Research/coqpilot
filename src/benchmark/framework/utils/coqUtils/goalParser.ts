import { ProofGoal } from "../../../../coqLsp/coqLspTypes";

import { toUnformattedJsonString } from "../../../../utils/printers";

export type SerializedGoal = string; // TODO: maybe develop proper serialized typing

export function serializeGoal(goal: ProofGoal): SerializedGoal {
    return toUnformattedJsonString(goal);
}

export function deserializeGoal(serializedGoal: SerializedGoal): ProofGoal {
    return JSON.parse(serializedGoal) as ProofGoal;
}

export function goalToProveAsString(goal: ProofGoal): string {
    return `${goal.ty}`;
}
