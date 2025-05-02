import { AbstractExternalServiceInstaller } from "../../../../llm/llmServices/abstractExternalService/installation/abstractExternalServiceInstaller";
import { provideDefaultInstallationForRequest } from "../../../../llm/llmServices/abstractExternalService/installation/wrappers";
import { RangoInstaller } from "../../../../llm/llmServices/rango/rangoInstaller";
import { UserModelParams } from "../../../../llm/userModelParams";

import { groupBy } from "../../../../utils/collectionUtils/mapUtils";
import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { logBySeverityLevelName } from "../../logging/wrappers";
import { LLMServiceIdentifier } from "../../structures/common/llmServiceIdentifier";
import { InputBenchmarkingBundle } from "../../structures/inputParameters/inputBenchmarkingBundle";

interface InstallerWithOptions<InstallationOptions> {
    installer: AbstractExternalServiceInstaller<InstallationOptions, any>;
    options?: InstallationOptions;
}

const EXTERNAL_SERVICES_TO_INSTALLERS_WITH_OPTIONS: Map<
    LLMServiceIdentifier,
    () => InstallerWithOptions<any>
> = new Map([
    [
        LLMServiceIdentifier.RANGO,
        () => {
            return {
                installer: new RangoInstaller(),
                options: undefined,
            };
        },
    ],
]);

export async function installDemandedExternalServices(
    inputBundles: InputBenchmarkingBundle[],
    logger: BenchmarkingLogger
) {
    const bundlesByService = groupBy(
        inputBundles,
        (bundle) => bundle.llmServiceIdentifier
    );
    for (const [
        llmServiceIdentifier,
        serviceBundles,
    ] of bundlesByService.entries()) {
        const installerProvider =
            EXTERNAL_SERVICES_TO_INSTALLERS_WITH_OPTIONS.get(
                llmServiceIdentifier
            );
        if (installerProvider === undefined) {
            continue;
        }
        const allInputParams = serviceBundles.flatMap(
            (bundle) => bundle.inputBenchmarkingModelsParams
        );
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
