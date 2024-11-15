import { Theorem } from "../../coqParser/parsedTypes";
import { CompletionContext } from "../completionGenerationContext";

export interface ContextTheoremsRanker {
    rankContextTheorems(
        theorems: Theorem[],
        completionContext: CompletionContext
    ): Theorem[];

    /**
     * _Note:_ so far it only triggers initial goals of all parsed theorems
     * being extracted at the parsing stage too.
     */
    needsUnwrappedNotations: boolean;
}
