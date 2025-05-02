import { getRootDir } from "../../../../utils/fs/rootResolvers";
import { UserModelParams } from "../../../userModelParams";

import { AbstractExternalServiceInstaller } from "./abstractExternalServiceInstaller";
import { InteractorMessageSeverity } from "./installationInteractor";
import { SimpleInstallationInteractor } from "./simpleInstallationInteractor";

export async function provideDefaultInstallationForRequest<
    InstallationOptions,
    InputModelParams extends UserModelParams,
>(
    installer: AbstractExternalServiceInstaller<InstallationOptions, any>,
    inputParams: InputModelParams[],
    inputOptions: InstallationOptions | undefined,
    showMessageImpl: (
        message: string,
        severity: InteractorMessageSeverity
    ) => void
) {
    await installer.provideInstallationForRequest(
        inputParams,
        getRootDir(),
        undefined,
        inputOptions,
        new SimpleInstallationInteractor(showMessageImpl, installer)
    );
}

export async function checkPrerequisitesAndInstallDefault<InstallationOptions>(
    installer: AbstractExternalServiceInstaller<InstallationOptions, any>,
    inputOptions: InstallationOptions,
    showMessageImpl: (
        message: string,
        severity: InteractorMessageSeverity
    ) => void
) {
    await installer.checkPrerequisitesAndInstall(
        getRootDir(),
        undefined,
        inputOptions,
        new SimpleInstallationInteractor(showMessageImpl, installer)
    );
}
