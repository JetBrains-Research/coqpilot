import { switchByLLMServiceType } from "../../llm/llmServices";
import { LLMService } from "../../llm/llmServices/llmService";

import {
    UIChoiceItemWithCallback,
    UIMessageSeverity,
    showMessageToUserWithSettingsHint,
} from "../ui/messages/editorMessages";
import { PLUGIN_ID } from "../utils/pluginId";

export class SettingsValidationError extends Error {
    private readonly otherChoiceItemsWithCallbacks: UIChoiceItemWithCallback[];

    constructor(
        errorMessage: string,
        private readonly messageToShowToUser: string,
        private readonly settingToOpenName: string = PLUGIN_ID,
        private readonly severity: UIMessageSeverity = "error",
        ...otherChoiceItemsWithCallbacks: UIChoiceItemWithCallback[]
    ) {
        super(errorMessage);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "SettingsValidationError";
        this.otherChoiceItemsWithCallbacks = otherChoiceItemsWithCallbacks;
    }

    showAsMessageToUser() {
        showMessageToUserWithSettingsHint(
            this.messageToShowToUser,
            this.severity,
            this.settingToOpenName,
            ...this.otherChoiceItemsWithCallbacks
        );
    }
}

export function toSettingName(llmService: LLMService<any, any>): string {
    const serviceNameInSettings = switchByLLMServiceType(
        llmService,
        () => "predefinedProofs",
        () => "openAi",
        () => "grazie",
        () => "lmStudio",
        () => "deepSeek",
        () => "rango"
    );
    return `${PLUGIN_ID}.${serviceNameInSettings}ModelsParameters`;
}
