import { exec } from "child_process";
import {
    ProgressLocation,
    ExtensionContext as VSCodeContext,
    window,
} from "vscode";

import { getOrCreateCoqPilotInstallationsDir } from "../../utils/fs/coqPilotInstallationsDir";
import { makeFileExecutable } from "../../utils/fs/fileUtils";
import { joinPaths } from "../../utils/fs/pathUtils";
import { PluginContext } from "../pluginContext";
import { showMessageToUser } from "../ui/messages/editorMessages";

namespace RangoScripts {
    export const RANGO_SCRIPTS_DIR = "scripts/rango";
    export const RANGO_INSTALLATION_SCRIPT_NAME = "setup-rango.sh";
    export const RANGO_UNINSTALLATION_SCRIPT_NAME = "uninstall-rango.sh";

    export function getScriptPath(
        action: "install" | "uninstall",
        coqPilotPath: string
    ): string {
        const scriptName =
            action === "install"
                ? RANGO_INSTALLATION_SCRIPT_NAME
                : RANGO_UNINSTALLATION_SCRIPT_NAME;
        return joinPaths(coqPilotPath, RANGO_SCRIPTS_DIR, scriptName);
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
    vscodeContext: VSCodeContext,
    pluginContext: PluginContext
) {
    window.withProgress(
        {
            location: ProgressLocation.Notification,
            title: "Installing the Rango project. Building dependencies may take a while...",
            cancellable: false,
        },
        async () => {
            getOrCreateCoqPilotInstallationsDir();
            return await installRango(
                vscodeContext.extensionPath,
                pluginContext.llmServices.rangoService.rangoDirPath
            );
        }
    );
}

async function installRango(
    coqPilotPath: string,
    rangoInstallationPath: string
) {
    return new Promise<void>((resolve, reject) => {
        const command = RangoScripts.prepareScriptExecutable(
            "install",
            coqPilotPath,
            rangoInstallationPath
        );
        exec(command, (error, stdout, stderr) => {
            if (error) {
                showMessageToUser(
                    `Rango installation failed: ${stderr || error.message} /// ${stdout}`,
                    "error"
                );
                reject(error);
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
    vscodeContext: VSCodeContext,
    pluginContext: PluginContext
) {
    window.withProgress(
        {
            location: ProgressLocation.Notification,
            title: "Uninstalling Rango project...",
            cancellable: false,
        },
        async () =>
            await uninstallRango(
                vscodeContext.extensionPath,
                pluginContext.llmServices.rangoService.rangoDirPath
            )
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
