import { AbstractExternalServiceInstaller } from "../../llm/llmServices/abstractExternalService/installation/abstractLLMServiceInstaller";
import {
    InstallationInteractor,
    InteractorChoiceItemWithCallback,
    InteractorMessageSeverity,
} from "../../llm/llmServices/abstractExternalService/installation/installationInteractor";

import { SettingsValidationError } from "../settings/settingsValidationError";
import {
    showMessageToUser,
    showMessageToUserWithActions,
} from "../ui/messages/editorMessages";
import { executeWithProgress } from "../ui/withProgressExecutor";
import { reportErrorToUser } from "../utils/errorHandlers";
import { PLUGIN_ID } from "../utils/pluginId";

export async function executeInstallationCommand<InstallationOptions>(
    coqPilotPath: string,
    installationPath: string,
    installationOptions: InstallationOptions,
    getInstaller: (
        installationPath: string
    ) => AbstractExternalServiceInstaller<InstallationOptions, any>
) {
    try {
        const installer = getInstaller(installationPath);
        await installer.checkPrerequisitesOrThrow();
        return executeWithProgress(
            `Installing the ${installer.externalProjectName} project. Building dependencies may take a while...`,
            async () =>
                installer.install(
                    coqPilotPath,
                    installationOptions,
                    new UserInstallationInteractor<InstallationOptions>(
                        getInstaller
                    )
                )
        );
    } catch (e) {
        reportErrorToUser(e);
    }
}

export async function executeUninstallationCommand<InstallationOptions>(
    coqPilotPath: string,
    installationPath: string,
    installationOptions: InstallationOptions,
    getInstaller: (
        installationPath: string
    ) => AbstractExternalServiceInstaller<InstallationOptions, any>
) {
    try {
        const installer = getInstaller(installationPath);
        return executeWithProgress(
            `Uninstalling the ${installer.externalProjectName} project...`,
            async () =>
                installer.uninstall(
                    coqPilotPath,
                    installationOptions,
                    new UserInstallationInteractor<InstallationOptions>(
                        getInstaller
                    )
                )
        );
    } catch (e) {
        reportErrorToUser(e);
    }
}

export class UserInstallationInteractor<InstallationOptions>
    implements InstallationInteractor<InstallationOptions>
{
    constructor(
        private readonly getInstaller: (
            installationPath: string
        ) => AbstractExternalServiceInstaller<InstallationOptions, any>
    ) {}

    async showMessage(message: string, severity: InteractorMessageSeverity) {
        showMessageToUser(message, severity);
    }

    async selectAndPerformInstallationAction(
        message: string,
        severity: InteractorMessageSeverity,
        ...choiceItemsWithCallbacks: InteractorChoiceItemWithCallback[]
    ) {
        await showMessageToUserWithActions(
            message,
            severity,
            ...choiceItemsWithCallbacks
        );
    }

    async selectAndPerformOutdatedInstallationsAction(
        message: string,
        severity: InteractorMessageSeverity,
        ...choiceItemsWithCallbacks: InteractorChoiceItemWithCallback[]
    ) {
        await showMessageToUserWithActions(
            message,
            severity,
            ...choiceItemsWithCallbacks
        );
    }

    async onCancelledInstallation(
        errorMessage: string,
        messageToShow: string,
        ...furtherChoiceItemsWithCallbacks: InteractorChoiceItemWithCallback[]
    ) {
        throw new SettingsValidationError(
            errorMessage,
            messageToShow,
            `${PLUGIN_ID}.rangoModelsParameters`,
            "error",
            ...furtherChoiceItemsWithCallbacks
        );
    }

    async performInstallation(
        coqPilotPath: string,
        installationPath: string,
        options: InstallationOptions
    ): Promise<void> {
        return executeInstallationCommand(
            coqPilotPath,
            installationPath,
            options,
            this.getInstaller
        );
    }

    async performUninstallation(
        coqPilotPath: string,
        installationPath: string,
        options: InstallationOptions
    ): Promise<void> {
        return executeUninstallationCommand(
            coqPilotPath,
            installationPath,
            options,
            this.getInstaller
        );
    }
}
