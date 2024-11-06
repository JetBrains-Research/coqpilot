import { Theorem } from "../../coqParser/parsedTypes";
import { CompletionContext } from "../completionGenerationContext";

export interface ContextTheoremsRanker {
    rankContextTheorems(
        theorems: Theorem[],
        completionContext: CompletionContext
    ): Theorem[];

    needsUnwrappedNotations: boolean;
}
