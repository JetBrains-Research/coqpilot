import { Theorem } from "../../coqParser/parsedTypes";
import { CompletionContext } from "../completionGenerationContext";

import { ContextTheoremsRanker } from "./contextTheoremsRanker";

export class RandomContextTheoremsRanker implements ContextTheoremsRanker {
    readonly needsUnwrappedNotations = false;

    private shuffleArray(array: any[]) {
        for (let i = array.length - 1; i > 0; i--) {
            const j = Math.floor(Math.random() * (i + 1));
            [array[i], array[j]] = [array[j], array[i]];
        }
    }

    rankContextTheorems(
        theorems: Theorem[],
        _completionContext: CompletionContext
    ): Theorem[] {
        const shuffledTheorems = theorems.slice();
        this.shuffleArray(shuffledTheorems);
        return shuffledTheorems;
    }
}
