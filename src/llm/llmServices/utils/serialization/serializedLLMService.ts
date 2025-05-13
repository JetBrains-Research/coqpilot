import { LLMServiceProvider } from "../../llmServiceProvider";

import { LLMServiceSerializer } from "./llmServiceSerializer";

export interface SerializedLLMService {
    serializationType: string;
    serializedData: string;
}

export function deserializeLLMService(
    serializedService: SerializedLLMService
): LLMServiceProvider {
    const serializationType = serializedService.serializationType;
    return LLMServiceSerializer.deserealizeBy(
        serializationType,
        serializedService.serializedData
    );
}
