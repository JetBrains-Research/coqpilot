import { expect } from "earl";

import { GeneratedRawContentItem } from "../../../proofProviders/impl/commonStructures/generatedRawContent";
import { ProofGenerationMetadataHolder } from "../../../proofProviders/impl/commonStructures/proofGenerationMetadata";
import { ProofGenerationType } from "../../../proofProviders/impl/commonStructures/proofGenerationType";
import { ProofVersion } from "../../../proofProviders/impl/commonStructures/proofVersion";

import { expectGeneratedProof } from "./expectGeneratedProof";
import { MockServiceGeneratedProof } from "./mockService";

export interface ExpectedGeneratedProofs {
    proofsToGenerateNumber: number;
    getProof: (index: number) => string;
    getVersionNumber: (index: number) => number;
    getProofVersions: (
        index: number,
        rawProofMetadata: GeneratedRawContentItem
    ) => ProofVersion[];
    getCanBeFixed: (index: number) => boolean;
}

export function expectSuccessfullyGeneratedProofs(
    generatedProofs: MockServiceGeneratedProof[],
    metadataHolder: ProofGenerationMetadataHolder,
    expected: ExpectedGeneratedProofs
) {
    expectSuccessfullyGeneratedItems<MockServiceGeneratedProof>(
        generatedProofs,
        metadataHolder,
        expected.proofsToGenerateNumber,
        expected.getProof,
        (generatedProof, rawProofMetadata, i, expectedProof) => {
            expectGeneratedProof(generatedProof, {
                proof: expectedProof,
                versionNumber: expected.getVersionNumber(i),
                rawProofMetadata: rawProofMetadata,
                proofVersions: expected.getProofVersions(i, rawProofMetadata),
                canBeFixed: expected.getCanBeFixed(i),
            });
        }
    );
}

export function expectSuccessfullyGeneratedItems<T>(
    generatedItems: T[],
    metadataHolder: ProofGenerationMetadataHolder,
    expectedItemsLength: number,
    getExpectedItem: (index: number) => string,
    testItem: (
        generatedItem: T,
        itemMetadata: GeneratedRawContentItem,
        index: number,
        expectedItem: string
    ) => void,
    isChatBasedGeneration: boolean = true
) {
    const successMetadata =
        metadataHolder.getSuccessfulProofGenerationMetadata();
    if (isChatBasedGeneration) {
        expect(successMetadata.proofGenerationType).toEqual(
            ProofGenerationType.CHAT_BASED
        );
        expect(successMetadata.analyzedChat).not.toBeNullish();
    }

    expect(generatedItems).toHaveLength(expectedItemsLength);
    expect(successMetadata.generatedRawProofs).toHaveLength(
        expectedItemsLength
    );
    for (let i = 0; i < generatedItems.length; i++) {
        const expectedItem = getExpectedItem(i);

        const rawProofMetadata = successMetadata.generatedRawProofs[i];
        expect(rawProofMetadata.content).toEqual(expectedItem);

        testItem(generatedItems[i], rawProofMetadata, i, expectedItem);
    }
}
