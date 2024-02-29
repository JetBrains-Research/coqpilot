import { LLMSequentialIterator } from "../../llm/llmIterator";
import { OpenAiService } from "../../llm/llmServices/openai/openAiService";
import { GrazieService } from "../../llm/llmServices/grazie/grazieService";
import { PredefinedProofsService } from "../../llm/llmServices/predefinedProofs/predefinedProofsService";
import { expect } from "earl";
import { ProofGenerationContext } from "../../llm/llmServices/modelParamsInterfaces";

suite("LLM Iterator test", () => {
    function getProofFromPredefinedCoqSentance(proof: string): string {
        return `Proof. ${proof} Qed.`;
    }

    test("Simple test of the iterator via predef proofs", async () => {
        const openAiService = new OpenAiService();
        const grazieService = new GrazieService();
        const predefinedProofsService = new PredefinedProofsService();
        const predefinedProofs = [
            "intros.",
            "reflexivity.",
            "auto.",
            "assumption. intros.",
            "left. reflexivity.",
        ];
        const modelsParams = {
            openAiParams: [],
            grazieParams: [],
            predefinedProofsModelParams: [
                {
                    tactics: predefinedProofs,
                },
            ],
        };
        const services = {
            openAiService,
            grazieService,
            predefinedProofsService,
        };
        const proofGenerationContext: ProofGenerationContext = {
            sameFileTheorems: [],
            admitCompletionTarget: "doesn't matter",
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
            expect(proof).toEqual(
                getProofFromPredefinedCoqSentance(predefinedProofs[i])
            );
            i++;
        }
    });
});
