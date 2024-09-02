import { ProofGoal } from "../../../../coqLsp/coqLspTypes";

export function serializeGoal(goal: ProofGoal): string {
    return JSON.stringify(goal);
}

export function deserializeGoal(serializedGoal: string): ProofGoal {
    return JSON.parse(serializedGoal) as ProofGoal;
}
