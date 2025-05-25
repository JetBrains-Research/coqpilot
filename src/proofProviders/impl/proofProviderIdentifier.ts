import { ExternalProofProviderParams } from "./abstractExternalProofProvider/abstractExternalProofProviderParams";
import { ProofProviderParams } from "./proofProviderParams";
import { ProofProviderCustomizationParams } from "./utils/proofProviderControlParams";

export enum ProofProviderIdentifier {
    PREDEFINED_PROOFS = "Predefined Proofs",
    OPENAI = "Open AI",
    GRAZIE = "Grazie",
    LMSTUDIO = "LM Studio",
    DEEPSEEK = "DeepSeek",
    RANGO = "Rango",
}

export type CorrespondingProofProviderParams<
    T extends ProofProviderIdentifier,
> = T extends ProofProviderIdentifier.PREDEFINED_PROOFS
    ? ProofProviderParams
    : T extends ProofProviderIdentifier.OPENAI
      ? ProofProviderParams
      : T extends ProofProviderIdentifier.GRAZIE
        ? ProofProviderParams
        : T extends ProofProviderIdentifier.LMSTUDIO
          ? ProofProviderParams
          : T extends ProofProviderIdentifier.DEEPSEEK
            ? ProofProviderParams
            : T extends ProofProviderIdentifier.RANGO
              ? ExternalProofProviderParams
              : never;

export type CorrespondingInputProofProviderParams<
    T extends ProofProviderIdentifier,
> = ProofProviderCustomizationParams<CorrespondingProofProviderParams<T>>;

export type ProofProviderStringIdentifier =
    | "predefined"
    | "openai"
    | "grazie"
    | "lmstudio"
    | "deepseek"
    | "rango";

export type CorrespondingIdentifier<T extends ProofProviderStringIdentifier> =
    T extends "predefined"
        ? ProofProviderIdentifier.PREDEFINED_PROOFS
        : T extends "openai"
          ? ProofProviderIdentifier.OPENAI
          : T extends "grazie"
            ? ProofProviderIdentifier.GRAZIE
            : T extends "lmstudio"
              ? ProofProviderIdentifier.LMSTUDIO
              : T extends "deepseek"
                ? ProofProviderIdentifier.DEEPSEEK
                : T extends "rango"
                  ? ProofProviderIdentifier.RANGO
                  : never;

export function toEnumIdentifier(
    stringIdentifier: ProofProviderStringIdentifier
): ProofProviderIdentifier {
    switch (stringIdentifier) {
        case "predefined":
            return ProofProviderIdentifier.PREDEFINED_PROOFS;
        case "openai":
            return ProofProviderIdentifier.OPENAI;
        case "grazie":
            return ProofProviderIdentifier.GRAZIE;
        case "lmstudio":
            return ProofProviderIdentifier.LMSTUDIO;
        case "deepseek":
            return ProofProviderIdentifier.DEEPSEEK;
        case "rango":
            return ProofProviderIdentifier.RANGO;
    }
}

/**
 * Regardless of the string values defined in the implementation of `ProofProviderIdentifier` (they can change with time),
 * this function guarantees to provide nice and human-readable names of the proofProviders.
 */
export function getShortName(
    proofProviderIdentifier: ProofProviderIdentifier
): string {
    switch (proofProviderIdentifier) {
        case ProofProviderIdentifier.PREDEFINED_PROOFS:
            return "Predefined Proofs";
        case ProofProviderIdentifier.OPENAI:
            return "Open AI";
        case ProofProviderIdentifier.GRAZIE:
            return "Grazie";
        case ProofProviderIdentifier.LMSTUDIO:
            return "LM Studio";
        case ProofProviderIdentifier.DEEPSEEK:
            return "DeepSeek";
        case ProofProviderIdentifier.RANGO:
            return "Rango";
    }
}
