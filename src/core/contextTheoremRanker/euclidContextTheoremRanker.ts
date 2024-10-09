import { Theorem } from "../../coqParser/parsedTypes";
import { CompletionContext } from "../completionGenerationContext";

import { ContextTheoremsRanker } from "./contextTheoremsRanker";
import { goalAsTheoremString } from "./tokenUtils";

/**
 * Ranks theorems based on how similar their statements are to
 * the current goal context. Metric is calculated on the
 * concatenated hypothesis and conclusion.
 *
 */
export class EuclidContextTheoremsRanker implements ContextTheoremsRanker {
    rankContextTheorems(
        theorems: Theorem[],
        completionContext: CompletionContext
    ): Theorem[] {
        const goal = completionContext.proofGoal;
        const goalTheorem = goalAsTheoremString(goal);

        const euclid = (theorem: Theorem): number => {
            const completionTokens = goalTheorem
                .split(" ")
                .filter(
                    (token) => token !== "#" && token !== ":" && token !== ""
                )
                .map((token) => token.replace(/[\(\).\n]/g, ""));
            const theoremTokens = goalAsTheoremString(theorem.initial_goal!!)
                .split(" ")
                .filter(
                    (token) => token !== "#" && token !== ":" && token !== ""
                )
                .map((token) => token.replace(/[\(\).\n]/g, ""));

            const intersection = completionTokens.filter((token) =>
                theoremTokens.includes(token)
            );

            const union = new Set([...completionTokens, ...theoremTokens]);

            return Math.sqrt(intersection.length - union.size);
        };

        return theorems.sort((a, b) => euclid(b) - euclid(a));
    }
}