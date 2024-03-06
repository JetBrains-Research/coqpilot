import { Theorem } from "../coqParser/parsedTypes";

export interface ProofGenerationContext {
    completionTarget: string;
    contextTheorems: Theorem[];
}
