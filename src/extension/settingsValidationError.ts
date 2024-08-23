import { switchByLLMServiceType } from "../llm/llmServices";
import { LLMService } from "../llm/llmServices/llmService";

import { pluginId } from "./coqPilot";
import {
    UIMessageSeverity,
    showMessageToUserWithSettingsHint,
} from "./editorMessages";

export class SettingsValidationError extends Error {
    constructor(
        errorMessage: string,
        private readonly messageToShowToUser: string,
        private readonly settingToOpenName: string = pluginId,
        private readonly severity: UIMessageSeverity = "error"
    ) {
        super(errorMessage);
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
