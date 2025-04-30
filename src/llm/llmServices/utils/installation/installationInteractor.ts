export type InteractorMessageSeverity = "error" | "info" | "warning";

export interface InteractorChoiceItemWithCallback {
    choiceItem: string;
    callback: () => Promise<void>;
}

export interface InstallationInteractor<ExtraInstallationOptions> {
    showMessage(
        message: string,
        severity: InteractorMessageSeverity
    ): Promise<void>;

    selectAndPerformInstallationAction(
        message: string,
        severity: InteractorMessageSeverity,
        ...choiceItemsWithCallbacks: InteractorChoiceItemWithCallback[]
    ): Promise<void>;

    selectAndPerformOutdatedInstallationsAction(
        message: string,
        severity: InteractorMessageSeverity,
        ...choiceItemsWithCallbacks: InteractorChoiceItemWithCallback[]
    ): Promise<void>;

    onCancelledInstallation(
        errorMessage: string,
        messageToShow: string,
        ...furtherChoiceItemsWithCallbacks: InteractorChoiceItemWithCallback[]
    ): Promise<void>;

    performInstallation(
        coqPilotPath: string,
        installationPath: string,
        extraOptions: ExtraInstallationOptions | undefined
    ): Promise<void>;

    performUninstallation(
        coqPilotPath: string,
        installationPath: string,
        extraOptions: ExtraInstallationOptions | undefined
    ): Promise<void>;
}
