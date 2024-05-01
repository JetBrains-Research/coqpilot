import { expect } from "earl";

import {
    GeneratedProof,
    ProofVersion,
} from "../../../llm/llmServices/llmService";

import { MockLLMGeneratedProof } from "./mockLLMService";

export interface ExpectedGeneratedProof {
    proof: string;
    versionNumber: number;
    proofVersions: ProofVersion[];
    nextVersionCanBeGenerated?: boolean;
    canBeFixed?: Boolean;
}

export function expectGeneratedProof(
    actual: GeneratedProof,
    expected: ExpectedGeneratedProof
) {
    const mockGeneratedProof = actual as MockLLMGeneratedProof;
    expect(mockGeneratedProof.proof()).toEqual(expected.proof);
    expect(mockGeneratedProof.versionNumber()).toEqual(expected.versionNumber);
    expect(mockGeneratedProof.proofVersions).toEqual(expected.proofVersions);
    if (expected.nextVersionCanBeGenerated !== undefined) {
        expect(mockGeneratedProof.nextVersionCanBeGenerated()).toEqual(
            expected.nextVersionCanBeGenerated
        );
    }
    if (expected.canBeFixed !== undefined) {
        expect(mockGeneratedProof.canBeFixed()).toEqual(expected.canBeFixed);
    }
}

export function toProofVersion(
    proof: string,
    diagnostic: string | undefined = undefined
): ProofVersion {
    return { proof: proof, diagnostic: diagnostic };
}
