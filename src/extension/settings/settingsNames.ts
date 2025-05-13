import { LLMServiceIdentifier } from "../../llm/llmServices/llmServiceIdentifier";

import { unsupported } from "../../utils/errors/throwErrors";
import { PLUGIN_ID } from "../utils/pluginId";

export function toSettingName(
    identifier: LLMServiceIdentifier | undefined
): string {
    const settingPrefix = toSettingPrefix(
        identifier ??
            unsupported("custom `LLMService`-s are not supported in the UI yet")
    );
    return `${PLUGIN_ID}.${settingPrefix}ModelsParameters`;
}

function toSettingPrefix(identifier: LLMServiceIdentifier): string {
    switch (identifier) {
        case LLMServiceIdentifier.PREDEFINED_PROOFS:
            return "predefinedProofs";
        case LLMServiceIdentifier.OPENAI:
            return "openAi";
        case LLMServiceIdentifier.GRAZIE:
            return "grazie";
        case LLMServiceIdentifier.LMSTUDIO:
            return "lmStudio";
        case LLMServiceIdentifier.DEEPSEEK:
            return "deepSeek";
        case LLMServiceIdentifier.RANGO:
            return "rango";
    }
}
