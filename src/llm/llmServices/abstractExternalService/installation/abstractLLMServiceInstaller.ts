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
import { ModelParams } from "../../modelParams";
import { AbstractExternalService } from "../abstractExternalService";

import { AbstractInstallationScriptsManager } from "./AbstractInstallationScriptsManager";
import { InstallationFailedError } from "./installationFailedError";
import { InstallationInteractor } from "./installationInteractor";
import {
    InstallationPrerequisite,
    checkAbstractPrerequisitesOrThrow,
} from "./prerequisitesChecker";

export abstract class AbstractExternalServiceInstaller<
    InstallationOptions,
    InputModelParams extends UserModelParams,
    ExternalServiceType extends AbstractExternalService<
        InputModelParams,
        ModelParams,
        InstallationOptions,
        any,
        any,
        any
    >,
> {
    abstract readonly externalService: ExternalServiceType;
    abstract readonly installationTargetName: string;

    abstract readonly installationPrerequisites: InstallationPrerequisite[];

    abstract scriptsManager: AbstractInstallationScriptsManager<InstallationOptions>;

    /**
     * Returns `undefined` if installation (available by `installationPath`)
     * is sufficient to execute `inputParams` models.
     * Otherwise returns `InstallationOptions` to perform installation with.
     */
    abstract checkInstallationIsAvailableForRequest(
        inputParams: InputModelParams[],
        installationPath: string,
        inputOptions: InstallationOptions
    ): InstallationOptions | undefined;

    abstract estimateInstallationTime(): string;

    protected readonly getDefaultInstallationDirPrefix = (): string => {
        return `coqpilot-${translateToSafeFileName(this.installationTargetName)}`;
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

        const installationPath = this.externalService.installationPath;
        const installationOptions = this.checkInstallationIsAvailableForRequest(
            inputParams,
            installationPath,
            inputOptions
        );
        if (installationOptions === undefined) {
            return;
        }

        await interactor.selectAndPerformInstallationAction(
            `${this.externalService.externalProjectName} models require the ${this.installationTargetName} project, which takes about ${this.estimateInstallationTime()} to install (one-time setup). Proceed with installation?`,
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
                        `${this.externalService.externalProjectName} models requested, but ${this.installationTargetName} is not installed and the user declined its installation`,
                        `${this.externalService.externalProjectName} models require the ${this.installationTargetName} project. Please run \`CoqPilot: Install and build ${this.installationTargetName} project\` or remove ${this.externalService.externalProjectName} models from the config, then try again.`,
                        {
                            choiceItem: `Install ${this.installationTargetName} now`,
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
            this.installationTargetName,
            this.installationPrerequisites
        );
    }

    async install(
        coqPilotPath: string,
        installationPath: string,
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
                            `${this.installationTargetName} installation failed: ${buildErrorCompleteLog(error)}.\nStderr:\n${stderr}`,
                            `${this.installationTargetName} installation failed: ${stderr || error.message}`
                        )
                    );
                } else {
                    interactor.showMessage(
                        `${this.installationTargetName} project has been succesfully installed at ${installationPath}`,
                        "info"
                    );
                    resolve();
                }
            });
        });
    }

    async uninstall(
        coqPilotPath: string,
        installationPath: string,
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
                        `${this.installationTargetName} uninstallation failed: ${stderr || error.message}`,
                        "error"
                    );
                    reject(error);
                } else {
                    interactor.showMessage(
                        `${this.installationTargetName} project has been succesfully uninstalled from ${installationPath}`,
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
                true &&
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
            this.externalService.installationPath
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
            `Outdated ${this.installationTargetName} projects have been successfully uninstalled.`,
            "info"
        );
    }

    private buildOutdatedInstallationsDetectedMessage(
        outdatedInstallationPaths: string[]
    ): string {
        const outdatedInstallationNames = outdatedInstallationPaths
            .map((dirPath) => getLastName(dirPath))
            .join(", ");
        return `Outdated ${this.installationTargetName} installations detected: ${outdatedInstallationNames}. They can't be used anymore. Would you like to uninstall them to free up space?`;
    }
}
