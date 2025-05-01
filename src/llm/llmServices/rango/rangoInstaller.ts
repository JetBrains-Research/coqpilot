import { exists } from "../../../utils/fs/pathUtils";
import { RangoUserModelParams } from "../../userModelParams";
import { AbstractInstallationScriptsManager } from "../abstractExternalService/installation/abstractInstallationScriptsManager";
import { AbstractExternalServiceInstaller } from "../abstractExternalService/installation/abstractLLMServiceInstaller";
import { InstallationPrerequisite } from "../abstractExternalService/installation/prerequisitesChecker";

import { RangoService } from "./rangoService";

// TODO: support model checkpoint installation
export interface RangoInstallationOptions {}

class RangoInstallationScriptsManager extends AbstractInstallationScriptsManager<RangoInstallationOptions> {
    readonly SCRIPTS_DIR = "scripts/rango";
    readonly INSTALLATION_SCRIPT_NAME = "setup-rango.sh";
    readonly UNINSTALLATION_SCRIPT_NAME = "uninstall-rango.sh";

    protected buildScriptExecutionCommand(
        scriptPath: string,
        installationPath: string,
        _options: RangoInstallationOptions
    ): string {
        return `${scriptPath} --rango_dir ${installationPath}`;
    }
}

export class RangoInstaller extends AbstractExternalServiceInstaller<
    RangoInstallationOptions,
    RangoUserModelParams,
    RangoService
> {
    constructor(rangoService: RangoService) {
        super(rangoService);
    }

    readonly installationPrerequisites: InstallationPrerequisite[] = [
        { name: "git", checkCommand: "git --version" },
        { name: "pyenv", checkCommand: "pyenv --version" },
    ];

    protected readonly scriptsManager = new RangoInstallationScriptsManager();

    checkInstallationIsAvailableForRequest(
        _inputParams: RangoUserModelParams[],
        installationPath: string,
        _inputOptions: RangoInstallationOptions
    ): RangoInstallationOptions | undefined {
        if (exists(installationPath)) {
            return undefined;
        }
        return {};
    }

    estimateInstallationTime(): string {
        return "5-10 minutes";
    }
}
