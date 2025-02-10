import { constructGenerationTokens } from "../../../llm/llmServices/commonStructures/generationTokens";
import { ProofVersion } from "../../../llm/llmServices/commonStructures/proofVersion";

import { approxCalculateTokens } from "./calculateTokens";

export function toMockProofVersion(
    proof: string,
    diagnostic: string | undefined = undefined
): ProofVersion {
    const mockRawContent = `Proof.\n${proof}\nQed.`;
    const mockTokensSpent = constructGenerationTokens(
        0,
        approxCalculateTokens(mockRawContent)
    );
    return {
        proof: proof,
        rawProof: {
            content: mockRawContent,
            tokensSpent: mockTokensSpent,
        },
        diagnostic: diagnostic,
    };
}
