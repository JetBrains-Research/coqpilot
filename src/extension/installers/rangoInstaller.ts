import { exec } from "child_process";
import { ProgressLocation, window } from "vscode";

import { RangoService } from "../../llm/llmServices/rango/rangoService";

import { buildErrorCompleteLog } from "../../utils/errors/errorsUtils";
import {
    getCoqPilotInstallationsDirPath,
    getOrCreateCoqPilotInstallationsDir,
} from "../../utils/fs/coqPilotInstallationsDir";
import { makeFileExecutable } from "../../utils/fs/fileUtils";
import { listFiles } from "../../utils/fs/listFiles";
import { exists } from "../../utils/fs/pathUtils";
import { getLastName, joinPaths } from "../../utils/fs/pathUtils";
import { showMessageToUser } from "../ui/messages/editorMessages";

import { InstallationFailedError } from "./installationFailedError";
import {
    InstallationPrerequisite,
    checkPrerequisitesOrThrow,
} from "./prerequisitesChecker";

namespace RangoScripts {
    export const SCRIPTS_DIR = "scripts/rango";
    export const INSTALLATION_SCRIPT_NAME = "setup-rango.sh";
    export const UNINSTALLATION_SCRIPT_NAME = "uninstall-rango.sh";

    export const prerequisites: InstallationPrerequisite[] = [
        { name: "git", checkCommand: "git --version" },
        { name: "pyenv", checkCommand: "pyenv --version" },
    ];

    export function getScriptPath(
        action: "install" | "uninstall",
        coqPilotPath: string
    ): string {
        const scriptName =
            action === "install"
                ? INSTALLATION_SCRIPT_NAME
                : UNINSTALLATION_SCRIPT_NAME;
        return joinPaths(coqPilotPath, SCRIPTS_DIR, scriptName);
    }

    export function buildScriptExecutionCommand(
        scriptPath: string,
        rangoDirPath: string
    ): string {
        return `${scriptPath} --rango_dir ${rangoDirPath}`;
    }

    export function prepareScriptExecutable(
        scriptAction: "install" | "uninstall",
        coqPilotPath: string,
        rangoPath: string
    ): string {
        const scriptPath = RangoScripts.getScriptPath(
            scriptAction,
            coqPilotPath
        );
        makeFileExecutable(scriptPath);
        return RangoScripts.buildScriptExecutionCommand(scriptPath, rangoPath);
    }
}

export async function executeRangoInstallationCommand(
    coqPilotPath: string,
    rangoInstallationPath: string
) {
    await checkPrerequisitesOrThrow("Rango", RangoScripts.prerequisites);
    return executeWithProgress(
        "Installing the Rango project. Building dependencies may take a while...",
        async () => installRango(coqPilotPath, rangoInstallationPath)
    );
}

async function installRango(
    coqPilotPath: string,
    rangoInstallationPath: string
) {
    return new Promise<void>((resolve, reject) => {
        getOrCreateCoqPilotInstallationsDir();
        const command = RangoScripts.prepareScriptExecutable(
            "install",
            coqPilotPath,
            rangoInstallationPath
        );
        // TODO: save stdout and stderr into logs (coqpilot meta dir)
        exec(command, (error, _, stderr) => {
            if (error) {
                reject(
                    new InstallationFailedError(
                        `Rango installation failed: ${buildErrorCompleteLog(error)}.\nStderr:\n${stderr}`,
                        `Rango installation failed: ${stderr || error.message}`
                    )
                );
            } else {
                showMessageToUser(
                    `Rango project has been succesfully installed at ${rangoInstallationPath}`
                );
                resolve();
            }
        });
    });
}

export async function executeRangoUninstallationCommand(
    coqPilotPath: string,
    rangoPath: string
) {
    return executeWithProgress("Uninstalling Rango project...", async () =>
        uninstallRango(coqPilotPath, rangoPath)
    );
}

async function uninstallRango(coqPilotPath: string, rangoPath: string) {
    return new Promise<void>((resolve, reject) => {
        const command = RangoScripts.prepareScriptExecutable(
            "uninstall",
            coqPilotPath,
            rangoPath
        );
        exec(command, (error, _, stderr) => {
            if (error) {
                showMessageToUser(
                    `Rango uninstallation failed: ${stderr || error.message}`,
                    "error"
                );
                reject(error);
            } else {
                showMessageToUser(
                    `Rango project has been succesfully uninstalled from ${rangoPath}`
                );
                resolve();
            }
        });
    });
}

async function executeWithProgress(title: string, block: () => Promise<void>) {
    return window.withProgress(
        {
            location: ProgressLocation.Notification,
            title: title,
            cancellable: false,
        },
        async () => block()
    );
}

export function detectOutdatedRangoInstallations(
    relevantRangoDirPath: string
): string[] {
    const installationDirPath = getCoqPilotInstallationsDirPath();
    if (!exists(installationDirPath)) {
        return [];
    }
    return listFiles(installationDirPath, 0, (filePath) => {
        const fileName = getLastName(filePath);
        return (
            true &&
            fileName.startsWith(RangoService.DEFAULT_RANGO_DIR_PREFIX) &&
            filePath !== relevantRangoDirPath
        );
    });
}
