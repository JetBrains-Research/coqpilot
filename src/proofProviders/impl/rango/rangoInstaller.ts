import { any } from "../../../utils/collectionUtils/listUtils";
import { exists, joinPaths } from "../../../utils/fs/pathUtils";
import { RangoUserModelParams } from "../../userModelParams";
import { AbstractInstallationScriptsManager } from "../abstractExternalProofProvider/installation/abstractInstallationScriptsManager";
import { AbstractProofProviderInstaller } from "../abstractExternalProofProvider/installation/abstractProofProviderInstaller";
import { InstallationPrerequisite } from "../abstractExternalProofProvider/installation/prerequisitesChecker";

export interface RangoInstallationOptions {
    enableModelCheckpointInstallation?: boolean;
}

class RangoInstallationScriptsManager extends AbstractInstallationScriptsManager<RangoInstallationOptions> {
    readonly SCRIPTS_DIR = "scripts/rango";
    readonly INSTALLATION_SCRIPT_NAME = "setup-rango.sh";
    readonly UNINSTALLATION_SCRIPT_NAME = "uninstall-rango.sh";

    protected buildScriptExecutionCommand(
        scriptPath: string,
        installationPath: string,
        options: RangoInstallationOptions
    ): string {
        const localModelInstallationFlag =
            options.enableModelCheckpointInstallation === true
                ? " --install_local_model"
                : "";
        return `${scriptPath} --rango_dir ${installationPath} ${localModelInstallationFlag}`;
    }
}

export class RangoInstaller extends AbstractProofProviderInstaller<
    RangoInstallationOptions,
    RangoUserModelParams
> {
    constructor() {
        super("Rango");
    }

    readonly installationPrerequisites: InstallationPrerequisite[] = [
        { name: "git", checkCommand: "git --version" },
        {
            name: "pyenv",
            checkCommand: [
                `export PYENV_ROOT="$HOME/.pyenv"`,
                `export PATH="$PYENV_ROOT/bin:$PATH"`,
                `eval "$(pyenv init -)"`,
                "pyenv --version",
            ].join(" && "),
        },
    ];

    protected readonly scriptsManager = new RangoInstallationScriptsManager();

    checkInstallationIsAvailableForRequest(
        inputParams: RangoUserModelParams[],
        installationPath: string,
        inputOptions: RangoInstallationOptions | undefined
    ): RangoInstallationOptions | undefined {
        const localModelInstallationRequired =
            any(inputParams, (params) => params.mode === "local") ||
            inputOptions?.enableModelCheckpointInstallation;
        const localModelIsMissing =
            localModelInstallationRequired &&
            !RangoInstaller.checkLocalModelCheckpointIsInstalled(
                installationPath
            );
        if (exists(installationPath)) {
            return localModelIsMissing
                ? { enableModelCheckpointInstallation: true }
                : undefined;
        } else {
            return {
                enableModelCheckpointInstallation:
                    localModelInstallationRequired,
            };
        }
    }

    estimateInstallationTime(): string {
        return "5-10 minutes";
    }

    private static readonly expectedLocalModelCheckpointRelativePath =
        "models/deepseek-bm25-proof-tfidf-proj-thm-prem-final";

    private static checkLocalModelCheckpointIsInstalled(
        installationPath: string
    ): boolean {
        return exists(
            joinPaths(
                installationPath,
                this.expectedLocalModelCheckpointRelativePath
            )
        );
    }
}
