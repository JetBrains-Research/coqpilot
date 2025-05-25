import { availableParallelism } from "os";

import {
    ResolvedProofProviderParams,
    resolveProofProviderParamsWithDefaults,
} from "../proofProviderParams";

import { AbstractExternalProofProvider } from "./abstractExternalProofProvider";

export type ExternalProofProviderParams =
    Partial<ResolvedExternalProofProviderParams>;

export interface ResolvedExternalProofProviderParams
    extends ResolvedProofProviderParams {
    readonly installationPath: string;
    readonly maxSubprocessesSpawnedInParallel: number;
    readonly clearProofGenerationLogsOnSuccess: boolean;

    /**
     * Is unused by `AbstractExternalProofProvider` by default.
     */
    readonly generationParallelism: number;
}

export function resolveExternalProofProviderParamsWithDefaults(
    proofProviderParams: ExternalProofProviderParams,
    externalProjectName: string,
    defaultMaxSubprocessesParallelism: number
): ResolvedExternalProofProviderParams {
    return {
        ...resolveProofProviderParamsWithDefaults(proofProviderParams),
        installationPath:
            proofProviderParams.installationPath ??
            AbstractExternalProofProvider.getDefaultInstallationPath(
                externalProjectName
            ),
        maxSubprocessesSpawnedInParallel:
            proofProviderParams.maxSubprocessesSpawnedInParallel ??
            Math.min(availableParallelism(), defaultMaxSubprocessesParallelism),
        clearProofGenerationLogsOnSuccess:
            proofProviderParams.clearProofGenerationLogsOnSuccess ?? true,
    };
}
