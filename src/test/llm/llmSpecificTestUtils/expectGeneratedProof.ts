import { expect } from "earl";

import { ProofVersion } from "../../../llm/llmServices/commonStructures/proofVersion";

import { MockLLMGeneratedProof } from "./mockLLMService";

export interface ExpectedGeneratedProof {
    proof: string;
    versionNumber: number;
    proofVersions: ProofVersion[];
    nextVersionCanBeGenerated?: boolean;
    canBeFixed?: Boolean;
}

export function expectGeneratedProof(
    actual: MockLLMGeneratedProof,
    expected: ExpectedGeneratedProof
) {
    expect(actual.proof()).toEqual(expected.proof);
    expect(actual.versionNumber()).toEqual(expected.versionNumber);
    expect(actual.proofVersions).toEqual(expected.proofVersions);
    if (expected.nextVersionCanBeGenerated !== undefined) {
        expect(actual.nextVersionCanBeGenerated()).toEqual(
            expected.nextVersionCanBeGenerated
        );
    }
    if (expected.canBeFixed !== undefined) {
        expect(actual.canBeFixed()).toEqual(expected.canBeFixed);
    }
}

export function toProofVersion(
    proof: string,
    diagnostic: string | undefined = undefined
): ProofVersion {
    return { proof: proof, diagnostic: diagnostic };
}
