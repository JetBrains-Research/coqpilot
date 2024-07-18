import { Goal, Hyp, PpString } from "../../coqLsp/coqLspTypes";

import { Theorem } from "../../coqParser/parsedTypes";
import { CompletionContext } from "../completionGenerationContext";

import { ContextTheoremsRanker } from "./contextTheoremsRanker";

/**
 * Ranks theorems based on how similar their statements are to
 * the current goal context. Metric is calculated on the
 * concatenated hypothesis and conclusion.
 *
 * ```J(A, B) = |A ∩ B| / |A ∪ B|```
 */
export class JaccardIndexContextTheoremsRanker
    implements ContextTheoremsRanker
{
    private hypToString(hyp: Hyp<PpString>): string {
        return `${hyp.names.join(" ")} : ${hyp.ty}`;
    }

    private goalAsTheorem(proofGoal: Goal<PpString>): string {
        const auxTheoremConcl = proofGoal?.ty;
        const theoremIndeces = proofGoal?.hyps
            .map((hyp) => `(${this.hypToString(hyp)})`)
            .join(" ");
        return `Theorem helper_theorem ${theoremIndeces} : ${auxTheoremConcl}.`;
    }

    rankContextTheorems(
        theorems: Theorem[],
        completionContext: CompletionContext
    ): Theorem[] {
        const goal = completionContext.proofGoal;
        const goalTheorem = this.goalAsTheorem(goal);

        const jaccardIndex = (theorem: Theorem): number => {
            const theoremStatement = theorem.statement;
            const completionTokens = goalTheorem.split(" ");
            const theoremTokens = theoremStatement.split(" ");

            const intersection = completionTokens.filter((token) =>
                theoremTokens.includes(token)
            );

            const union = new Set([...completionTokens, ...theoremTokens]);

            return intersection.length / union.size;
        };

        return theorems.sort((a, b) => jaccardIndex(b) - jaccardIndex(a));
    }
}
