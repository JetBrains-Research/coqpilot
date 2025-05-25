import { AbstractProofProviderInstaller } from "../abstractExternalProofProvider/installation/abstractProofProviderInstaller";

export interface InstallerWithOptions<InstallationOptions> {
    installer: AbstractProofProviderInstaller<InstallationOptions, any>;
    options?: InstallationOptions;
}

export type InstallerProvider = () => InstallerWithOptions<any>;
