import { CompletionContext } from "../completionGenerator";
import { Theorem } from "../../coqParser/parsedTypes";

export interface ContextTheoremsRankerInterface {
    rankContextTheorems(
        theorems: Theorem[],
        completionContext: CompletionContext
    ): Theorem[];
}
