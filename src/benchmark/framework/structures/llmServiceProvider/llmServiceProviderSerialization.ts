import { LLMServiceProvider } from "./llmServiceProvider";

export interface SerializedLLMServiceProvider {
    serializationType: string;
    serializedData: string;
}

export function serializeLLMServiceProvider(
    serviceProvider: LLMServiceProvider
): SerializedLLMServiceProvider {
    return {
        serializationType: serviceProvider.getSerializationType(),
        serializedData: serviceProvider.serializeData(),
    };
}

export function deserializeLLMServiceProvider(
    serializedServiceProvider: SerializedLLMServiceProvider
): LLMServiceProvider {
    const serializationType = serializedServiceProvider.serializationType;
    return LLMServiceProvider.deserealizeBy(
        serializationType,
        serializedServiceProvider.serializedData
    );
}
