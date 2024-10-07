import { Goal, Hyp, PpString } from "../../coqLsp/coqLspTypes";

import { Theorem } from "../../coqParser/parsedTypes";
import { CompletionContext } from "../completionGenerator";

import { ContextTheoremsRanker } from "./contextTheoremsRanker";

/**
 * Ranks theorems based on how similar their statements are to
 * the current goal context. Metric is calculated on the
 * concatenated hypothesis and conclusion.
 *
 */
export class EuclidContextTheoremsRanker implements ContextTheoremsRanker {
    private hypToString(hyp: Hyp<PpString>): string {
        return `${hyp.names.join(" ")} : ${hyp.ty}`;
    }

    private goalAsTheorem(proofGoal: Goal<PpString>): string {
        const auxTheoremConcl = proofGoal?.ty;
        const theoremIndeces = proofGoal?.hyps
            .map((hyp) => `(${this.hypToString(hyp)})`)
            .join(" ");
        return `${theoremIndeces} # ${auxTheoremConcl}.`;
    }

    rankContextTheorems(
        theorems: Theorem[],
        completionContext: CompletionContext
    ): Theorem[] {
        console.log("EUCLID IS USED");
        const goal = completionContext.proofGoal;
        const goalTheorem = this.goalAsTheorem(goal);

        const euclid = (theorem: Theorem): number => {
            const completionTokens = goalTheorem
                .split(" ")
                .filter(
                    (token) => token !== "#" && token !== ":" && token !== ""
                )
                .map((token) => token.replace(/[\(\).\n]/g, ""));
            const theoremTokens = this.goalAsTheorem(theorem.initial_goal!!)
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
