import { AbstractExternalServiceInstaller } from "../../../../llm/llmServices/abstractExternalService/installation/abstractExternalServiceInstaller";

export interface InstallerWithOptions<InstallationOptions> {
    installer: AbstractExternalServiceInstaller<InstallationOptions, any>;
    options?: InstallationOptions;
}

export type InstallerProvider = () => InstallerWithOptions<any>;
