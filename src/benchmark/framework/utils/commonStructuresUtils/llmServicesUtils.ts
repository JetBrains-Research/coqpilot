import { LLMServiceIdentifier } from "../../structures/common/llmServiceIdentifier";

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

export interface LLMServicesItems<ItemType> {
    predefinedProofs: ItemType;
    openAi: ItemType;
    grazie: ItemType;
    lmStudio: ItemType;
    deepSeek: ItemType;
    rango: ItemType;
}

export function selectLLMServiceItem<ItemType>(
    serviceIdentifier: LLMServiceIdentifier,
    items: LLMServicesItems<ItemType>
): ItemType {
    switch (serviceIdentifier) {
        case LLMServiceIdentifier.PREDEFINED_PROOFS:
            return items.predefinedProofs;
        case LLMServiceIdentifier.OPENAI:
            return items.openAi;
        case LLMServiceIdentifier.GRAZIE:
            return items.grazie;
        case LLMServiceIdentifier.LMSTUDIO:
            return items.lmStudio;
        case LLMServiceIdentifier.DEEPSEEK:
            return items.deepSeek;
        case LLMServiceIdentifier.RANGO:
            return items.rango;
    }
}

export class LLMServicesItemsHolder<ItemType>
    implements LLMServicesItems<ItemType>
{
    readonly predefinedProofs!: ItemType;
    readonly openAi!: ItemType;
    readonly grazie!: ItemType;
    readonly lmStudio!: ItemType;
    readonly deepSeek!: ItemType;
    readonly rango!: ItemType;

    constructor(items: LLMServicesItems<ItemType>) {
        Object.assign(this, items);
    }

    select(serviceIdentifier: LLMServiceIdentifier): ItemType {
        return selectLLMServiceItem(serviceIdentifier, this);
    }
}
