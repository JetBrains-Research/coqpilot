import { AnalyzedChatHistory } from "../../../llm/llmServices/commonStructures/chat";
import { ProofGenerationContext } from "../../../llm/proofGenerationContext";

export const proofsToGenerate = [
    "auto.",
    "left. reflexivity.",
    "right. auto.",
    "intros.",
    "assumption.",
    "something.",
    "",
    "reflexivity.",
    "auto.",
    "auto.",
];

export const testModelId = "test model";

export const gptModelName = "gpt-4o-mini-2024-07-18";

export const mockChat: AnalyzedChatHistory = {
    chat: [{ role: "system", content: "Generate proofs." }],
    contextTheorems: [],
    estimatedTokens: {
        messagesTokens: 10,
        maxTokensToGenerate: 50,
        maxTokensInTotal: 60,
    },
};

export const mockProofGenerationContext: ProofGenerationContext = {
    completionTarget: "forall n : nat, 0 + n = n",
    contextTheorems: [],
};
