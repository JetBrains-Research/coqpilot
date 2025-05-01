import { exec } from "child_process";

import { buildErrorCompleteLog } from "../../../../utils/errors/errorsUtils";
import {
    getCoqPilotInstallationsDirPath,
    getOrCreateCoqPilotInstallationsDir,
} from "../../../../utils/fs/coqPilotInstallationsDir";
import { listFiles } from "../../../../utils/fs/listFiles";
import { exists, getLastName } from "../../../../utils/fs/pathUtils";
import { UserModelParams } from "../../../userModelParams";
import { AbstractExternalService } from "../abstractExternalService";

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
    constructor(readonly externalProjectName: string) {}

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

    getDefaultInstallationPath(): string {
        return AbstractExternalService.getDefaultInstallationPath(
            this.externalProjectName
        );
    }

    async provideInstallationForRequest(
        inputParams: InputModelParams[],
        coqPilotPath: string,
        installationPath: string = this.getDefaultInstallationPath(),
        inputOptions: InstallationOptions,
        interactor: InstallationInteractor<InstallationOptions>
    ) {
        if (inputParams.length === 0) {
            return;
        }
        await this.detectAndSuggestRemovingOutdatedInstallations(
            coqPilotPath,
            installationPath,
            inputOptions,
            interactor
        );

        const installationOptions = this.checkInstallationIsAvailableForRequest(
            inputParams,
            installationPath,
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
                        installationPath,
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
                                    installationPath,
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
        installationPath: string = this.getDefaultInstallationPath(),
        options: InstallationOptions,
        interactor: InstallationInteractor<InstallationOptions>
    ) {
        return new Promise<void>((resolve, reject) => {
            getOrCreateCoqPilotInstallationsDir();
            const command = this.scriptsManager.prepareScriptExecutable(
                "install",
                coqPilotPath,
                installationPath,
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
                        `${this.externalProjectName} project has been succesfully installed at ${installationPath}`,
                        "info"
                    );
                    resolve();
                }
            });
        });
    }

    async uninstall(
        coqPilotPath: string,
        installationPath: string = this.getDefaultInstallationPath(),
        options: InstallationOptions,
        interactor: InstallationInteractor<InstallationOptions>
    ) {
        return new Promise<void>((resolve, reject) => {
            const command = this.scriptsManager.prepareScriptExecutable(
                "uninstall",
                coqPilotPath,
                installationPath,
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
                        `${this.externalProjectName} project has been succesfully uninstalled from ${installationPath}`,
                        "info"
                    );
                    resolve();
                }
            });
        });
    }

    async checkPrerequisitesAndInstall(
        coqPilotPath: string,
        installationPath: string = this.getDefaultInstallationPath(),
        options: InstallationOptions,
        interactor: InstallationInteractor<InstallationOptions>
    ) {
        await this.checkPrerequisitesOrThrow();
        await this.install(coqPilotPath, installationPath, options, interactor);
    }

    detectOutdatedInstallations(
        relevantInstallationPath: string = this.getDefaultInstallationPath()
    ): string[] {
        const installationDirPath = getCoqPilotInstallationsDirPath();
        if (!exists(installationDirPath)) {
            return [];
        }
        return listFiles(installationDirPath, 0, (filePath) => {
            const fileName = getLastName(filePath);
            return (
                fileName.startsWith(
                    AbstractExternalService.getDefaultInstallationDirPrefix(
                        this.externalProjectName
                    )
                ) && filePath !== relevantInstallationPath
            );
        });
    }

    async detectAndSuggestRemovingOutdatedInstallations(
        coqPilotPath: string,
        relevantInstallationPath: string = this.getDefaultInstallationPath(),
        extraOptions: InstallationOptions,
        interactor: InstallationInteractor<InstallationOptions>
    ) {
        const outdatedInstallations = this.detectOutdatedInstallations(
            relevantInstallationPath
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
