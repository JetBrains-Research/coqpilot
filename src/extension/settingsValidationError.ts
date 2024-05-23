import { commands } from "vscode";

import { switchByLLMServiceType } from "../llm/llmServices";
import { LLMService } from "../llm/llmServices/llmService";

import { pluginId } from "./coqPilot";
import { UIMessageSeverity, showMessageToUser } from "./editorMessages";

export const openSettingsItem = "Open settings";

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

export function showMessageToUserWithSettingsHint(
    message: string,
    severity: UIMessageSeverity,
    settingToOpenName: string = pluginId
) {
    showMessageToUser(message, severity, openSettingsItem).then((value) => {
        if (value === openSettingsItem) {
            commands.executeCommand(
                "workbench.action.openSettings",
                settingToOpenName
            );
        }
    });
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
