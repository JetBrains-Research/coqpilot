import { expect } from "earl";

import { GeneratedRawContentItem } from "../../../proofProviders/impl/commonStructures/generatedRawContent";
import { ProofVersion } from "../../../proofProviders/impl/commonStructures/proofVersion";

import { MockServiceGeneratedProof } from "./mockService";

export interface ExpectedGeneratedProof {
    proof: string;
    versionNumber: number;
    rawProofMetadata: GeneratedRawContentItem;
    proofVersions: ProofVersion[];
    nextVersionCanBeGenerated?: boolean;
    canBeFixed?: Boolean;
}

export function expectGeneratedProof(
    actual: MockServiceGeneratedProof,
    expected: ExpectedGeneratedProof
) {
    expect(actual.proof).toEqual(expected.proof);
    expect(actual.versionNumber).toEqual(expected.versionNumber);

    expect(actual.rawProof.content).toEqual(expected.rawProofMetadata.content);
    expect(actual.rawProof.tokensSpent).toEqual(
        expected.rawProofMetadata.tokensSpent
    );

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
    rawProofMetadata: GeneratedRawContentItem,
    diagnostic: string | undefined = undefined
): ProofVersion {
    return { proof: proof, rawProof: rawProofMetadata, diagnostic: diagnostic };
}
