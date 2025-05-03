import { availableParallelism } from "os";

import {
    ResolvedLLMServiceParams,
    resolveServiceParamsWithDefaults,
} from "../llmServiceParams";

import { AbstractExternalService } from "./abstractExternalService";

export type ExternalServiceParams = Partial<ResolvedExternalServiceParams>;

export interface ResolvedExternalServiceParams
    extends ResolvedLLMServiceParams {
    installationPath: string;
    maxSubprocessesSpawnedInParallel: number;
    clearProofGenerationLogsOnSuccess: boolean;
}

export function resolveExternalServiceParamsWithDefaults(
    serviceParams: ExternalServiceParams,
    externalProjectName: string,
    defaultMaxSubprocessesParallelism: number
): ResolvedExternalServiceParams {
    return {
        ...resolveServiceParamsWithDefaults(serviceParams),
        installationPath:
            serviceParams.installationPath ??
            AbstractExternalService.getDefaultInstallationPath(
                externalProjectName
            ),
        maxSubprocessesSpawnedInParallel:
            serviceParams.maxSubprocessesSpawnedInParallel ??
            Math.min(availableParallelism(), defaultMaxSubprocessesParallelism),
        clearProofGenerationLogsOnSuccess:
            serviceParams.clearProofGenerationLogsOnSuccess ?? true,
    };
}
