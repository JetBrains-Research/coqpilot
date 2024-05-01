import { expect } from "earl";

import { LLMSequentialIterator } from "../../llm/llmIterator";
import { disposeServices } from "../../llm/llmServices";
import { GeneratedProof } from "../../llm/llmServices/llmService";
import { ProofGenerationContext } from "../../llm/proofGenerationContext";

import {
    createDefaultServices,
    createPredefinedProofsModel,
    createTrivialModelsParams,
} from "../commonTestFunctions/defaultLLMServicesBuilder";

suite("LLM Iterator test", () => {
    const predefinedModel1 = createPredefinedProofsModel("first model");
    const predefinedModel2 = createPredefinedProofsModel("second model");
    const modelsParams = createTrivialModelsParams([
        predefinedModel1,
        predefinedModel2,
    ]);
    const tactics = predefinedModel1.tactics;
    const tacticsAsProofs = tactics.map((tactic) => `Proof. ${tactic} Qed.`);

    const proofGenerationContext: ProofGenerationContext = {
        contextTheorems: [],
        completionTarget: "doesn't matter",
    };

    test("Test `nextProof` via two predefined-proofs models", async () => {
        const services = createDefaultServices();
        try {
            const iterator = new LLMSequentialIterator(
                proofGenerationContext,
                modelsParams,
                services
            );
            for (let i = 0; i < 2; i++) {
                for (let t = 0; t < tactics.length; t++) {
                    const result = await iterator.nextProof();
                    expect(result.done).toBeFalsy();
                    const proof = result.value;
                    expect(proof.proof()).toEqual(tacticsAsProofs[t]);
                }
            }
            const result = await iterator.nextProof();
            expect(result.done);
        } finally {
            disposeServices(services);
        }
    });

    test("Test `next` via two predefined-proofs models", async () => {
        const services = createDefaultServices();
        try {
            const iterator = new LLMSequentialIterator(
                proofGenerationContext,
                modelsParams,
                services
            );
            for (let i = 0; i < 2; i++) {
                const result = await iterator.next();
                expect(result.done).toBeFalsy();
                const proofsBatch = result.value.map(
                    (proofObject: GeneratedProof) => proofObject.proof()
                );
                expect(proofsBatch).toEqual(tacticsAsProofs);
            }
            const result = await iterator.next();
            expect(result.done);
        } finally {
            disposeServices(services);
        }
    });
});
