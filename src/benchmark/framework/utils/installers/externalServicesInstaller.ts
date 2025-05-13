import { provideDefaultInstallationForRequest } from "../../../../llm/llmServices/abstractExternalService/installation/wrappers";
import { InstallerWithOptions } from "../../../../llm/llmServices/commonStructures/installerProvider";
import { UserModelParams } from "../../../../llm/userModelParams";

import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { logBySeverityLevelName } from "../../logging/wrappers";
import { ResolvedWithServiceBenchmarkingBundle } from "../../structures/inputParameters/resolvedWithServiceBenchmarkingBundle";

export async function installDemandedExternalServices(
    resolvedBundles: ResolvedWithServiceBenchmarkingBundle[],
    logger: BenchmarkingLogger
) {
    /**
     * Note: no check for duplicate installations needed, since each of the `llmService` instances
     * of `resolvedBundles` is unique.
     */
    for (const bundle of resolvedBundles) {
        const installerProvider = bundle.llmService.installerProvider;
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
