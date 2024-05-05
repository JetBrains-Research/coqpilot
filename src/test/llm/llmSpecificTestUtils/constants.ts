import { AnalyzedChatHistory } from "../../../llm/llmServices/chat";
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

export const gptTurboModelName = "gpt-3.5-turbo-0301";

export const mockChat: AnalyzedChatHistory = {
    chat: [{ role: "system", content: "Generate proofs." }],
    estimatedTokens: 10,
};

export const mockProofGenerationContext: ProofGenerationContext = {
    completionTarget: "forall n : nat, 0 + n = n",
    contextTheorems: [],
};
