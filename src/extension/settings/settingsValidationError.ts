import { switchByLLMServiceType } from "../../llm/llmServices";
import { LLMService } from "../../llm/llmServices/llmService";

import {
    UIMessageSeverity,
    showMessageToUserWithSettingsHint,
} from "../ui/messages/editorMessages";
import { pluginId } from "../utils/pluginId";

export class SettingsValidationError extends Error {
    constructor(
        errorMessage: string,
        private readonly messageToShowToUser: string,
        private readonly settingToOpenName: string = pluginId,
        private readonly severity: UIMessageSeverity = "error"
    ) {
        super(errorMessage);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "SettingsValidationError";
    }

    showAsMessageToUser() {
        showMessageToUserWithSettingsHint(
            this.messageToShowToUser,
            this.severity,
            this.settingToOpenName
        );
    }
}

export function toSettingName(llmService: LLMService<any, any>): string {
    const serviceNameInSettings = switchByLLMServiceType(
        llmService,
        () => "predefinedProofs",
        () => "openAi",
        () => "grazie",
        () => "lmStudio"
    );
    return `${pluginId}.${serviceNameInSettings}ModelsParameters`;
}
