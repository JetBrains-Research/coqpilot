import { makeFileExecutable } from "../../../../utils/fs/fileUtils";
import { joinPaths } from "../../../../utils/fs/pathUtils";

export abstract class AbstractLLMServiceInstallationScriptsManager<
    ExtraInstallationOptions,
> {
    abstract readonly SCRIPTS_DIR: string;
    abstract readonly INSTALLATION_SCRIPT_NAME: string;
    abstract readonly UNINSTALLATION_SCRIPT_NAME: string;

    prepareScriptExecutable(
        scriptAction: "install" | "uninstall",
        coqPilotPath: string,
        installationPath: string,
        extraOptions: ExtraInstallationOptions
    ): string {
        const scriptPath = this.getScriptPath(scriptAction, coqPilotPath);
        makeFileExecutable(scriptPath);
        return this.buildScriptExecutionCommand(
            scriptPath,
            installationPath,
            extraOptions
        );
    }

    protected getScriptPath(
        action: "install" | "uninstall",
        coqPilotPath: string
    ): string {
        const scriptName =
            action === "install"
                ? this.INSTALLATION_SCRIPT_NAME
                : this.UNINSTALLATION_SCRIPT_NAME;
        return joinPaths(coqPilotPath, this.SCRIPTS_DIR, scriptName);
    }

    protected abstract buildScriptExecutionCommand(
        scriptPath: string,
        installationPath: string,
        extraOptions: ExtraInstallationOptions
    ): string;
}
