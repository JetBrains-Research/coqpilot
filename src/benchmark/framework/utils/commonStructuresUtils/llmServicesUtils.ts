import { LLMServiceStringIdentifier } from "../../structures/common/llmServiceIdentifier";

/**
 * Regardless of the string values defined in the implementation of `LLMServiceIdentifier` (they can change with time),
 * this function guarantees to provide nice and human-readable names of the services.
 */
export function getShortName(
    serviceIdentifier: LLMServiceStringIdentifier
): string {
    switch (serviceIdentifier) {
        case "predefined":
            return "Predefined Proofs";
        case "openai":
            return "Open AI";
        case "grazie":
            return "Grazie";
        case "lmstudio":
            return "LM Studio";
        case "deepseek":
            return "DeepSeek";
        case "rango":
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
    serviceIdentifier: LLMServiceStringIdentifier,
    items: LLMServicesItems<ItemType>
): ItemType {
    switch (serviceIdentifier) {
        case "predefined":
            return items.predefinedProofs;
        case "openai":
            return items.openAi;
        case "grazie":
            return items.grazie;
        case "lmstudio":
            return items.lmStudio;
        case "deepseek":
            return items.deepSeek;
        case "rango":
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

    select(serviceIdentifier: LLMServiceStringIdentifier): ItemType {
        return selectLLMServiceItem(serviceIdentifier, this);
    }
}
