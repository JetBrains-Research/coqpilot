import { ProofProviderIdentifier } from "../../proofProviders/impl/proofProviderIdentifier";

import { unsupported } from "../../utils/errors/throwErrors";
import { PLUGIN_ID } from "../utils/pluginId";

export function toSettingName(
    identifier: ProofProviderIdentifier | undefined
): string {
    const settingPrefix = toSettingPrefix(
        identifier ??
            unsupported(
                "custom `ProofProvider`-s are not supported in the UI yet"
            )
    );
    return `${PLUGIN_ID}.${settingPrefix}ModelsParameters`;
}

function toSettingPrefix(identifier: ProofProviderIdentifier): string {
    switch (identifier) {
        case ProofProviderIdentifier.PREDEFINED_PROOFS:
            return "predefinedProofs";
        case ProofProviderIdentifier.OPENAI:
            return "openAi";
        case ProofProviderIdentifier.GRAZIE:
            return "grazie";
        case ProofProviderIdentifier.LMSTUDIO:
            return "lmStudio";
        case ProofProviderIdentifier.DEEPSEEK:
            return "deepSeek";
        case ProofProviderIdentifier.RANGO:
            return "rango";
    }
}
