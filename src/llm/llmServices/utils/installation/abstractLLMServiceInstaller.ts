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
import { LLMService } from "../../llmService";
import { ModelParams } from "../../modelParams";

import { AbstractLLMServiceInstallationScriptsManager } from "./abstractLLMServiceInstallationScriptsManager";
import { InstallationFailedError } from "./installationFailedError";
import { InstallationInteractor } from "./installationInteractor";
import {
    InstallationPrerequisite,
    checkAbstractPrerequisitesOrThrow,
} from "./prerequisitesChecker";

export abstract class AbstractLLMServiceInstaller<
    ExtraInstallationOptions,
    InputModelParams extends UserModelParams,
    LLMServiceType extends LLMService<InputModelParams, ModelParams>,
> {
    abstract readonly llmService: LLMServiceType;
    abstract readonly installationTargetName: string;

    abstract readonly installationPrerequisites: InstallationPrerequisite[];

    abstract scriptsManager: AbstractLLMServiceInstallationScriptsManager<ExtraInstallationOptions>;

    /**
     * Returns `undefined` if installation (available by `installationPath`)
     * is sufficient to execute `inputParams` models.
     * Otherwise returns `ExtraInstallationOptions` to perform installation with.
     */
    abstract checkInstallationIsAvailableForRequest(
        inputParams: InputModelParams[],
        installationPath: string,
        inputExtraOptions: ExtraInstallationOptions
    ): ExtraInstallationOptions | undefined;

    abstract estimateInstallationTime(): string;

    readonly getDefaultInstallationDirPrefix = (): string => {
        return `coqpilot-${translateToSafeFileName(this.installationTargetName)}`;
    };

    readonly getDefaultInstallationRepoDirName = (): string => {
        return `${this.getDefaultInstallationDirPrefix()}-v${PLUGIN_VERSION}`;
    };

    readonly getInstallationPath = (): string => {
        return joinPaths(
            getCoqPilotInstallationsDirPath(),
            this.getDefaultInstallationRepoDirName()
        );
    };

    async provideInstallationForRequest(
        inputParams: InputModelParams[],
        coqPilotPath: string,
        inputExtraOptions: ExtraInstallationOptions,
        interactor: InstallationInteractor<ExtraInstallationOptions>
    ) {
        if (inputParams.length === 0) {
            return;
        }
        await this.detectAndSuggestRemovingOutdatedInstallations(
            coqPilotPath,
            inputExtraOptions,
            interactor
        );

        // TODO: support getting path from the external proof provider service
        const installationPath = this.getInstallationPath();
        const extraOptions = this.checkInstallationIsAvailableForRequest(
            inputParams,
            installationPath,
            inputExtraOptions
        );
        if (extraOptions === undefined) {
            return;
        }

        await interactor.selectAndPerformInstallationAction(
            `${this.llmService.serviceName} models require the ${this.installationTargetName} project, which takes about ${this.estimateInstallationTime()} to install (one-time setup). Proceed with installation?`,
            "info",
            {
                choiceItem: "Install",
                callback: async () =>
                    await interactor.performInstallation(
                        coqPilotPath,
                        installationPath,
                        extraOptions
                    ),
            },
            {
                choiceItem: "Cancel",
                callback: async () => {
                    await interactor.onCancelledInstallation(
                        `${this.llmService.serviceName} models requested, but ${this.installationTargetName} is not installed and the user declined its installation`,
                        `${this.llmService.serviceName} models require the ${this.installationTargetName} project. Please run \`CoqPilot: Install and build ${this.installationTargetName} project\` or remove ${this.llmService.serviceName} models from the config, then try again.`,
                        {
                            choiceItem: `Install ${this.installationTargetName} now`,
                            callback: async () =>
                                interactor.performInstallation(
                                    coqPilotPath,
                                    installationPath,
                                    extraOptions
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
        extraOptions: ExtraInstallationOptions,
        interactor: InstallationInteractor<ExtraInstallationOptions>
    ) {
        return new Promise<void>((resolve, reject) => {
            getOrCreateCoqPilotInstallationsDir();
            const command = this.scriptsManager.prepareScriptExecutable(
                "install",
                coqPilotPath,
                installationPath,
                extraOptions
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
        extraOptions: ExtraInstallationOptions,
        interactor: InstallationInteractor<ExtraInstallationOptions>
    ) {
        return new Promise<void>((resolve, reject) => {
            const command = this.scriptsManager.prepareScriptExecutable(
                "uninstall",
                coqPilotPath,
                installationPath,
                extraOptions
            );
            exec(command, (error, _, stderr) => {
                if (error) {
                    interactor.showMessage(
                        `Rango uninstallation failed: ${stderr || error.message}`,
                        "error"
                    );
                    reject(error);
                } else {
                    interactor.showMessage(
                        `Rango project has been succesfully uninstalled from ${installationPath}`,
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
        extraOptions: ExtraInstallationOptions | undefined,
        interactor: InstallationInteractor<ExtraInstallationOptions>
    ) {
        // TODO: support getting path from the external proof provider service
        const outdatedInstallations = this.detectOutdatedInstallations(
            this.getInstallationPath()
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
        extraOptions: ExtraInstallationOptions | undefined,
        interactor: InstallationInteractor<ExtraInstallationOptions>
    ) {
        for (const installationPath of outdatedInstallationPaths) {
            await interactor.performUninstallation(
                coqPilotPath,
                installationPath,
                extraOptions
            );
        }
        interactor.showMessage(
            "Outdated Rango projects have been successfully uninstalled.",
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
