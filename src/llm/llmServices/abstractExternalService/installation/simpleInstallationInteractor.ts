import { invariantFailed } from "../../../../utils/errors/throwErrors";

import { AbstractExternalServiceInstaller } from "./abstractExternalServiceInstaller";
import {
    InstallationInteractor,
    InteractorChoiceItemWithCallback,
    InteractorMessageSeverity,
} from "./installationInteractor";

export class SimpleInstallationInteractor<InstallationOptions>
    implements InstallationInteractor<InstallationOptions>
{
    constructor(
        private readonly showMessageImpl: (
            message: string,
            severity: InteractorMessageSeverity
        ) => void,
        private readonly installer: AbstractExternalServiceInstaller<
            InstallationOptions,
            any
        >
    ) {}

    async showMessage(message: string, severity: InteractorMessageSeverity) {
        this.showMessageImpl(message, severity);
    }

    async selectAndPerformInstallationAction(
        message: string,
        severity: InteractorMessageSeverity,
        installItem: InteractorChoiceItemWithCallback,
        _cancelItem: InteractorChoiceItemWithCallback
    ) {
        this.showMessageImpl(
            `${message}\nSimple installation interactor: Installation will be performed.`,
            severity
        );
        await installItem.callback();
    }

    async selectAndPerformOutdatedInstallationsAction(
        message: string,
        severity: InteractorMessageSeverity,
        _freeUpSpaceItem: InteractorChoiceItemWithCallback,
        skipForNowItem: InteractorChoiceItemWithCallback
    ) {
        this.showMessageImpl(
            `${message}\nSimple installation interactor: Skip for now.`,
            severity
        );
        await skipForNowItem.callback();
    }

    onCancelledInstallation(
        _errorMessage: string,
        _messageToShow: string,
        _installItem: InteractorChoiceItemWithCallback
    ): Promise<void> {
        invariantFailed(
            "Simple installation interactor",
            "the cancellation of the installation is not expected to be triggered"
        );
    }

    performInstallation(
        coqPilotPath: string,
        installationPath: string,
        options: InstallationOptions
    ): Promise<void> {
        return this.installer.install(
            coqPilotPath,
            installationPath,
            options,
            this
        );
    }

    performUninstallation(
        coqPilotPath: string,
        installationPath: string,
        options: InstallationOptions
    ): Promise<void> {
        return this.installer.uninstall(
            coqPilotPath,
            installationPath,
            options,
            this
        );
    }
}
