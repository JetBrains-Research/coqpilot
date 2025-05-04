import { provideDefaultInstallationForRequest } from "../../../../llm/llmServices/abstractExternalService/installation/wrappers";
import { UserModelParams } from "../../../../llm/userModelParams";

import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { logBySeverityLevelName } from "../../logging/wrappers";
import { InputBenchmarkingBundle } from "../../structures/inputParameters/inputBenchmarkingBundle";
import { InstallerWithOptions } from "../../structures/llmServiceProvider/installerProvider";

export async function installDemandedExternalServices(
    inputBundles: InputBenchmarkingBundle[],
    logger: BenchmarkingLogger
) {
    /**
     * Note: this implementation does not optimize duplicate installations
     * for the duplicate service providers from different bundles;
     * however, that:
     * a) is a rare case, since all the targets needed for the specific service can be defined in one bundle;
     * b) even if an effective duplicate is present, the installer would reuse the already existing installation.
     */
    for (const bundle of inputBundles) {
        const installerProvider =
            bundle.llmServiceProvider.getInstallerProvider();
        if (installerProvider === undefined) {
            continue;
        }
        const allInputParams = bundle.inputBenchmarkingModelsParams;
        await checkInstallationIsSufficientOrInstall(
            installerProvider(),
            allInputParams,
            logger
        );
    }
}

async function checkInstallationIsSufficientOrInstall<InstallationOptions>(
    installerWithOptions: InstallerWithOptions<InstallationOptions>,
    allInputParams: UserModelParams[],
    logger: BenchmarkingLogger
) {
    const { installer, options } = installerWithOptions;
    const installationLogger = logger.createChildLoggerWithIdentifier(
        `[External project installation: ${installer.externalProjectName}]`
    );
    installationLogger.debug(
        `${installer.externalProjectName} installation is demanded, checking...`
    );
    await provideDefaultInstallationForRequest(
        installer,
        allInputParams,
        options,
        (message, severity) =>
            logBySeverityLevelName(installationLogger, severity, message)
    );
    installationLogger.debug(
        `${installer.externalProjectName} installation is verified to be sufficient`
    );
}
