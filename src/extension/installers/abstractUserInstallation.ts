import { AbstractProofProviderInstaller } from "../../proofProviders/impl/abstractExternalProofProvider/installation/abstractProofProviderInstaller";
import {
    InstallationInteractor,
    InteractorChoiceItemWithCallback,
    InteractorMessageSeverity,
} from "../../proofProviders/impl/abstractExternalProofProvider/installation/installationInteractor";

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
    installationOptions: InstallationOptions,
    installer: AbstractProofProviderInstaller<InstallationOptions, any>,
    installationPath: string = installer.getDefaultInstallationPath()
) {
    try {
        await installer.checkPrerequisitesOrThrow();
        return executeWithProgress(
            `Installing the ${installer.externalProjectName} project. Building dependencies may take a while...`,
            async () =>
                installer.install(
                    coqPilotPath,
                    installationPath,
                    installationOptions,
                    new UserInstallationInteractor<InstallationOptions>(
                        installer
                    )
                )
        );
    } catch (e) {
        reportErrorToUser(e);
    }
}

export async function executeUninstallationCommand<InstallationOptions>(
    coqPilotPath: string,
    installationOptions: InstallationOptions,
    installer: AbstractProofProviderInstaller<InstallationOptions, any>,
    installationPath: string = installer.getDefaultInstallationPath()
) {
    try {
        return executeWithProgress(
            `Uninstalling the ${installer.externalProjectName} project...`,
            async () =>
                installer.uninstall(
                    coqPilotPath,
                    installationPath,
                    installationOptions,
                    new UserInstallationInteractor<InstallationOptions>(
                        installer
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
        private readonly installer: AbstractProofProviderInstaller<
            InstallationOptions,
            any
        >
    ) {}

    async showMessage(message: string, severity: InteractorMessageSeverity) {
        showMessageToUser(message, severity);
    }

    async selectAndPerformInstallationAction(
        message: string,
        severity: InteractorMessageSeverity,
        installItem: InteractorChoiceItemWithCallback,
        cancelItem: InteractorChoiceItemWithCallback
    ) {
        await showMessageToUserWithActions(
            message,
            severity,
            installItem,
            cancelItem
        );
    }

    async selectAndPerformOutdatedInstallationsAction(
        message: string,
        severity: InteractorMessageSeverity,
        freeUpSpaceItem: InteractorChoiceItemWithCallback,
        skipForNowItem: InteractorChoiceItemWithCallback
    ) {
        await showMessageToUserWithActions(
            message,
            severity,
            freeUpSpaceItem,
            skipForNowItem
        );
    }

    async onCancelledInstallation(
        errorMessage: string,
        messageToShow: string,
        installItem: InteractorChoiceItemWithCallback
    ) {
        throw new SettingsValidationError(
            errorMessage,
            messageToShow,
            `${PLUGIN_ID}.rangoModelsParameters`,
            "error",
            installItem
        );
    }

    async performInstallation(
        coqPilotPath: string,
        installationPath: string,
        options: InstallationOptions
    ): Promise<void> {
        return executeInstallationCommand(
            coqPilotPath,
            options,
            this.installer,
            installationPath
        );
    }

    async performUninstallation(
        coqPilotPath: string,
        installationPath: string,
        options: InstallationOptions
    ): Promise<void> {
        return executeUninstallationCommand(
            coqPilotPath,
            options,
            this.installer,
            installationPath
        );
    }
}
