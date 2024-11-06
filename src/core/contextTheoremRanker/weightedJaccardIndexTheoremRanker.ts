import { Theorem } from "../../coqParser/parsedTypes";
import { CompletionContext } from "../completionGenerationContext";

import { ContextTheoremsRanker } from "./contextTheoremsRanker";
import { goalAsTheoremString } from "./tokenUtils";

/**
 * Ranks theorems based on how similar their statements are to
 * the current goal context. Metric is calculated on the
 * concatenated hypothesis and conclusion.
 *
 * // TODO: metric description?
 */
export class WeightedJaccardIndexContextTheoremsRanker
    implements ContextTheoremsRanker
{
    readonly needsUnwrappedNotations = true;

    rankContextTheorems(
        theorems: Theorem[],
        completionContext: CompletionContext
    ): Theorem[] {
        const goal = completionContext.proofGoal;
        const goalTheorem = goalAsTheoremString(goal);

        const allTokens = theorems
            .map((theorem) => {
                return goalAsTheoremString(theorem.initial_goal!!)
                    .split(" ")
                    .filter(
                        (token) =>
                            token !== "#" && token !== ":" && token !== ""
                    )
                    .map((token) => token.replace(/[\(\).\n]/g, ""));
            })
            .flat();

        const weightedJaccardIndex = (theorem: Theorem): number => {
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

            const tfidfIntersection = intersection
                .map((token) => tfidf(allTokens, token))
                .reduce((a, b) => a + b, 0);
            const tfidfUnion = Array.from(union.values())
                .map((token) => tfidf(allTokens, token))
                .reduce((a, b) => a + b, 0);

            return tfidfIntersection / tfidfUnion;
        };

        return theorems.sort(
            (a, b) => weightedJaccardIndex(b) - weightedJaccardIndex(a)
        );
    }
}

function tfidf(allTokens: string[], token: string): number {
    const count = allTokens.filter((t) => t === token).length;
    return count / allTokens.length;
}
