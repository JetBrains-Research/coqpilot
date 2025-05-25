export type InteractorMessageSeverity = "error" | "info" | "warning";

export interface InteractorChoiceItemWithCallback {
    choiceItem: string;
    callback: () => Promise<void>;
}

export interface InstallationInteractor<InstallationOptions> {
    showMessage(
        message: string,
        severity: InteractorMessageSeverity
    ): Promise<void>;

    selectAndPerformInstallationAction(
        message: string,
        severity: InteractorMessageSeverity,
        installItem: InteractorChoiceItemWithCallback,
        cancelItem: InteractorChoiceItemWithCallback
    ): Promise<void>;

    selectAndPerformOutdatedInstallationsAction(
        message: string,
        severity: InteractorMessageSeverity,
        freeUpSpaceItem: InteractorChoiceItemWithCallback,
        skipForNowItem: InteractorChoiceItemWithCallback
    ): Promise<void>;

    onCancelledInstallation(
        errorMessage: string,
        messageToShow: string,
        installItem: InteractorChoiceItemWithCallback
    ): Promise<void>;

    performInstallation(
        coqPilotPath: string,
        installationPath: string,
        options: InstallationOptions
    ): Promise<void>;

    performUninstallation(
        coqPilotPath: string,
        installationPath: string,
        options: InstallationOptions
    ): Promise<void>;
}
