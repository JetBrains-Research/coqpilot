import { getOrPut } from "../utils/collectionUtils/mapUtils";
import { illegalState } from "../utils/errors/throwErrors";

import { ProofProvider } from "./impl/proofProvider";
import { ProofProviderIdentifier } from "./impl/proofProviderIdentifier";

export class ProofProvidersStorage {
    private readonly identifierToProofProviders: Map<
        ProofProviderIdentifier,
        ProofProvider[]
    > = new Map();
    private readonly customProofProviders: ProofProvider[] = [];

    registerProofProvider(
        newProofProviderBuilder: () => ProofProvider
    ): ProofProvider {
        const newProofProvider = newProofProviderBuilder();
        const identifier = newProofProvider.identifier;

        const proofProvidersOfSameType =
            identifier === undefined
                ? this.customProofProviders
                : getOrPut(
                      this.identifierToProofProviders,
                      identifier,
                      () => [] as ProofProvider[]
                  );
        for (const existingProofProvider of proofProvidersOfSameType) {
            if (newProofProvider.isSameInstance(existingProofProvider)) {
                newProofProvider.dispose();
                illegalState(
                    `Failed to register new proofProvider: ${newProofProvider.toLogString(false)}; `,
                    `since its instance already exists: ${existingProofProvider.toLogString(false)}. `,
                    `Make sure your proofProviders of the same type are supposed to be different instances. `,
                    `If it is not the case, use only one of them instead.`
                );
            }
        }
        proofProvidersOfSameType.push(newProofProvider as any);

        return newProofProvider;
    }

    dispose() {
        for (const proofProviders of this.identifierToProofProviders.values()) {
            for (const proofProvider of proofProviders) {
                proofProvider.dispose();
            }
        }
    }

    getProofProviders(
        identifier: ProofProviderIdentifier | undefined
    ): ProofProvider[] {
        if (identifier === undefined) {
            return this.customProofProviders;
        } else {
            return this.identifierToProofProviders.get(identifier) ?? [];
        }
    }

    allProofProviders(): ProofProvider[] {
        return [
            ...Array.from(this.identifierToProofProviders.values()).flat(),
            ...this.customProofProviders,
        ];
    }
}
