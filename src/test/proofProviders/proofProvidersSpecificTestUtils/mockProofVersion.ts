import { constructGenerationTokens } from "../../../proofProviders/impl/commonStructures/generationTokens";
import { ProofVersion } from "../../../proofProviders/impl/commonStructures/proofVersion";

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
