import { expect } from "earl";

import { LLMSequentialIterator } from "../../llm/llmIterator";
import { GrazieService } from "../../llm/llmServices/grazie/grazieService";
import { LMStudioService } from "../../llm/llmServices/lmStudio/lmStudioService";
import { OpenAiService } from "../../llm/llmServices/openai/openAiService";
import { PredefinedProofsService } from "../../llm/llmServices/predefinedProofs/predefinedProofsService";
import { ProofGenerationContext } from "../../llm/proofGenerationContext";
import { UserModelsParams } from "../../llm/userModelParams";

suite("LLM Iterator test", () => {
    function getProofFromPredefinedCoqSentance(proof: string): string {
        return `Proof. ${proof} Qed.`;
    }

    test("Simple test of the iterator via predef proofs", async () => {
        const openAiService = new OpenAiService();
        const grazieService = new GrazieService();
        const predefinedProofsService = new PredefinedProofsService();
        const lmStudioService = new LMStudioService();
        const predefinedProofs = [
            "intros.",
            "reflexivity.",
            "auto.",
            "assumption. intros.",
            "left. reflexivity.",
        ];
        const modelsParams: UserModelsParams = {
            openAiParams: [],
            grazieParams: [],
            predefinedProofsModelParams: [
                {
                    modelName: "Doesn't matter",
                    tactics: predefinedProofs,
                },
            ],
            lmStudioParams: [],
        };
        const services = {
            openAiService,
            grazieService,
            predefinedProofsService,
            lmStudioService,
        };
        const proofGenerationContext: ProofGenerationContext = {
            contextTheorems: [],
            completionTarget: "doesn't matter",
        };
        const iterator = new LLMSequentialIterator(
            proofGenerationContext,
            modelsParams,
            services
        );

        let i = 0;
        while (true) {
            const result = await iterator.nextProof();
            if (result.done) {
                break;
            }
            const proof = result.value;
            expect(proof.proof()).toEqual(
                getProofFromPredefinedCoqSentance(predefinedProofs[i])
            );
            i++;
        }
    });
});
