import { exec } from "child_process";

import { PLUGIN_VERSION } from "../../../../extension/utils/pluginId";
import { buildErrorCompleteLog } from "../../../../utils/errors/errorsUtils";
import {
    getCoqPilotInstallationsDirPath,
    getOrCreateCoqPilotInstallationsDir,
} from "../../../../utils/fs/coqPilotInstallationsDir";
import { translateToSafeFileName } from "../../../../utils/fs/fileNameUtils";
import { listFiles } from "../../../../utils/fs/listFiles";
import { exists, getLastName, joinPaths } from "../../../../utils/fs/pathUtils";
import { UserModelParams } from "../../../userModelParams";

import { AbstractInstallationScriptsManager } from "./abstractInstallationScriptsManager";
import { InstallationFailedError } from "./installationFailedError";
import { InstallationInteractor } from "./installationInteractor";
import {
    InstallationPrerequisite,
    checkAbstractPrerequisitesOrThrow,
} from "./prerequisitesChecker";

export abstract class AbstractExternalServiceInstaller<
    InstallationOptions,
    InputModelParams extends UserModelParams,
> {
    readonly installationPath: string;

    constructor(
        readonly externalProjectName: string,
        installationPath: string | undefined = undefined
    ) {
        this.installationPath =
            installationPath ?? this.getDefaultInstallationPath();
    }

    abstract constructInstaller(
        installationPath: string
    ): AbstractExternalServiceInstaller<InstallationOptions, InputModelParams>;

    abstract readonly installationPrerequisites: InstallationPrerequisite[];

    protected abstract readonly scriptsManager: AbstractInstallationScriptsManager<InstallationOptions>;

    /**
     * Returns `undefined` if installation (available by `installationPath`)
     * is sufficient to execute `inputParams` models.
     * Otherwise returns `InstallationOptions` to perform installation with.
     */
    protected abstract checkInstallationIsAvailableForRequest(
        inputParams: InputModelParams[],
        installationPath: string,
        inputOptions: InstallationOptions
    ): InstallationOptions | undefined;

    abstract estimateInstallationTime(): string;

    protected readonly getDefaultInstallationDirPrefix = (): string => {
        return `coqpilot-${translateToSafeFileName(this.externalProjectName)}`;
    };

    protected readonly getDefaultInstallationRepoDirName = (): string => {
        return `${this.getDefaultInstallationDirPrefix()}-v${PLUGIN_VERSION}`;
    };

    readonly getDefaultInstallationPath = (): string => {
        return joinPaths(
            getCoqPilotInstallationsDirPath(),
            this.getDefaultInstallationRepoDirName()
        );
    };

    async provideInstallationForRequest(
        inputParams: InputModelParams[],
        coqPilotPath: string,
        inputOptions: InstallationOptions,
        interactor: InstallationInteractor<InstallationOptions>
    ) {
        if (inputParams.length === 0) {
            return;
        }
        await this.detectAndSuggestRemovingOutdatedInstallations(
            coqPilotPath,
            inputOptions,
            interactor
        );

        const installationOptions = this.checkInstallationIsAvailableForRequest(
            inputParams,
            this.installationPath,
            inputOptions
        );
        if (installationOptions === undefined) {
            return;
        }

        await interactor.selectAndPerformInstallationAction(
            `${this.externalProjectName} models require the ${this.externalProjectName} project, which takes about ${this.estimateInstallationTime()} to install (one-time setup). Proceed with installation?`,
            "info",
            {
                choiceItem: "Install",
                callback: async () =>
                    await interactor.performInstallation(
                        coqPilotPath,
                        this.installationPath,
                        installationOptions
                    ),
            },
            {
                choiceItem: "Cancel",
                callback: async () => {
                    await interactor.onCancelledInstallation(
                        `${this.externalProjectName} models requested, but ${this.externalProjectName} is not installed and the user declined its installation`,
                        `${this.externalProjectName} models require the ${this.externalProjectName} project. Please run \`CoqPilot: Install and build ${this.externalProjectName} project\` or remove ${this.externalProjectName} models from the config, then try again.`,
                        {
                            choiceItem: `Install ${this.externalProjectName} now`,
                            callback: async () =>
                                interactor.performInstallation(
                                    coqPilotPath,
                                    this.installationPath,
                                    installationOptions
                                ),
                        }
                    );
                },
            }
        );
    }

    async checkPrerequisitesOrThrow() {
        await checkAbstractPrerequisitesOrThrow(
            this.externalProjectName,
            this.installationPrerequisites
        );
    }

    async install(
        coqPilotPath: string,
        options: InstallationOptions,
        interactor: InstallationInteractor<InstallationOptions>
    ) {
        return new Promise<void>((resolve, reject) => {
            getOrCreateCoqPilotInstallationsDir();
            const command = this.scriptsManager.prepareScriptExecutable(
                "install",
                coqPilotPath,
                this.installationPath,
                options
            );
            // TODO: save stdout and stderr into logs (coqpilot meta dir)
            exec(command, (error, _, stderr) => {
                if (error) {
                    reject(
                        new InstallationFailedError(
                            `${this.externalProjectName} installation failed: ${buildErrorCompleteLog(error)}.\nStderr:\n${stderr}`,
                            `${this.externalProjectName} installation failed: ${stderr || error.message}`
                        )
                    );
                } else {
                    interactor.showMessage(
                        `${this.externalProjectName} project has been succesfully installed at ${this.installationPath}`,
                        "info"
                    );
                    resolve();
                }
            });
        });
    }

    async uninstall(
        coqPilotPath: string,
        options: InstallationOptions,
        interactor: InstallationInteractor<InstallationOptions>
    ) {
        return new Promise<void>((resolve, reject) => {
            const command = this.scriptsManager.prepareScriptExecutable(
                "uninstall",
                coqPilotPath,
                this.installationPath,
                options
            );
            exec(command, (error, _, stderr) => {
                if (error) {
                    interactor.showMessage(
                        `${this.externalProjectName} uninstallation failed: ${stderr || error.message}`,
                        "error"
                    );
                    reject(error);
                } else {
                    interactor.showMessage(
                        `${this.externalProjectName} project has been succesfully uninstalled from ${this.installationPath}`,
                        "info"
                    );
                    resolve();
                }
            });
        });
    }

    detectOutdatedInstallations(relevantInstallationDirPath: string): string[] {
        const installationDirPath = getCoqPilotInstallationsDirPath();
        if (!exists(installationDirPath)) {
            return [];
        }
        return listFiles(installationDirPath, 0, (filePath) => {
            const fileName = getLastName(filePath);
            return (
                fileName.startsWith(this.getDefaultInstallationDirPrefix()) &&
                filePath !== relevantInstallationDirPath
            );
        });
    }

    async detectAndSuggestRemovingOutdatedInstallations(
        coqPilotPath: string,
        extraOptions: InstallationOptions,
        interactor: InstallationInteractor<InstallationOptions>
    ) {
        const outdatedInstallations = this.detectOutdatedInstallations(
            this.installationPath
        );
        if (outdatedInstallations.length === 0) {
            return;
        }
        await interactor.selectAndPerformOutdatedInstallationsAction(
            this.buildOutdatedInstallationsDetectedMessage(
                outdatedInstallations
            ),
            "warning",
            {
                choiceItem: "Free up space",
                callback: async () => {
                    await this.uninstallOutdatedInstallations(
                        outdatedInstallations,
                        coqPilotPath,
                        extraOptions,
                        interactor
                    );
                },
            },
            {
                choiceItem: "Skip for now",
                callback: async () => {},
            }
        );
    }

    private async uninstallOutdatedInstallations(
        outdatedInstallationPaths: string[],
        coqPilotPath: string,
        options: InstallationOptions,
        interactor: InstallationInteractor<InstallationOptions>
    ) {
        for (const installationPath of outdatedInstallationPaths) {
            await interactor.performUninstallation(
                coqPilotPath,
                installationPath,
                options
            );
        }
        interactor.showMessage(
            `Outdated ${this.externalProjectName} projects have been successfully uninstalled.`,
            "info"
        );
    }

    private buildOutdatedInstallationsDetectedMessage(
        outdatedInstallationPaths: string[]
    ): string {
        const outdatedInstallationNames = outdatedInstallationPaths
            .map((dirPath) => getLastName(dirPath))
            .join(", ");
        return `Outdated ${this.externalProjectName} installations detected: ${outdatedInstallationNames}. They can't be used anymore. Would you like to uninstall them to free up space?`;
    }
}
