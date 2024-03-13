import { Theorem } from "../../coqParser/parsedTypes";
import { CompletionContext } from "../completionGenerator";

export interface ContextTheoremsRanker {
    rankContextTheorems(
        theorems: Theorem[],
        completionContext: CompletionContext
    ): Theorem[];
}
