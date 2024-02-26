import { CompletionContext } from "../completionGenerator";
import { Theorem } from "../../coqParser/parsedTypes";

export interface ContextTheoremsRanker {
    rankContextTheorems(
        theorems: Theorem[],
        completionContext: CompletionContext
    ): Theorem[];
}
