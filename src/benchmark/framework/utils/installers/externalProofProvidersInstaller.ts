import { provideDefaultInstallationForRequest } from "../../../../proofProviders/impl/abstractExternalProofProvider/installation/wrappers";
import { InstallerWithOptions } from "../../../../proofProviders/impl/commonStructures/installerProvider";
import { UserModelParams } from "../../../../proofProviders/userModelParams";

import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { logBySeverityLevelName } from "../../logging/wrappers";
import { ResolvedWithProofProviderBenchmarkingBundle } from "../../structures/inputParameters/resolvedWithProofProviderBenchmarkingBundle";

export async function installDemandedExternalProofProviders(
    resolvedBundles: ResolvedWithProofProviderBenchmarkingBundle[],
    logger: BenchmarkingLogger
) {
    /**
     * Note: no check for duplicate installations needed, since each of the `proofProvider` instances
     * of `resolvedBundles` is unique.
     */
    for (const bundle of resolvedBundles) {
        const installerProvider = bundle.proofProvider.installerProvider;
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
