import { ProofProviderConstructor } from "../../proofProviderConstructor";

import { ProofProviderSerializer } from "./proofProviderSerializer";

export interface SerializedProofProvider {
    serializationType: string;
    serializedData: string;
}

export function deserializeProofProvider(
    serializedProofProvider: SerializedProofProvider
): ProofProviderConstructor {
    const serializationType = serializedProofProvider.serializationType;
    return ProofProviderSerializer.deserealizeBy(
        serializationType,
        serializedProofProvider.serializedData
    );
}
