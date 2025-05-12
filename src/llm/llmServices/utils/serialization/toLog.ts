import { JsonSpacing, toJsonString } from "../../../../utils/printers";
import { LLMServiceIdentifier } from "../../llmServiceIdentifier";

export function toOneLineLogString(
    shortName: string,
    providerData: any,
    verbose: boolean
): string {
    const serviceParamsString =
        providerData === undefined || !verbose
            ? ""
            : ` ${toJsonString(providerData, JsonSpacing.UNFORMATTED)}`;
    return `${shortName}${serviceParamsString}`;
}

/**
 * Regardless of the string values defined in the implementation of `LLMServiceIdentifier` (they can change with time),
 * this function guarantees to provide nice and human-readable names of the services.
 */
export function getShortName(serviceIdentifier: LLMServiceIdentifier): string {
    switch (serviceIdentifier) {
        case LLMServiceIdentifier.PREDEFINED_PROOFS:
            return "Predefined Proofs";
        case LLMServiceIdentifier.OPENAI:
            return "Open AI";
        case LLMServiceIdentifier.GRAZIE:
            return "Grazie";
        case LLMServiceIdentifier.LMSTUDIO:
            return "LM Studio";
        case LLMServiceIdentifier.DEEPSEEK:
            return "DeepSeek";
        case LLMServiceIdentifier.RANGO:
            return "Rango";
    }
}
