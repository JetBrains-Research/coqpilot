import { EventLogger } from "../../logging/eventLogger";

import { ErrorsHandlingMode } from "./commonStructures/errorsHandlingMode";

/**
 * @property `eventLogger` is used to send proof generation events. If not specified, event logging will be disabled.
 * @proptery `errorsHandlingMode` defines how errors during method calls are handled: whether they are rethrown or swallowed. Regardless of the mode, errors are logged. By default, `ErrorsHandlingMode.RETHROW_ERRORS`.
 * @property `generationParallelism` defines max number of parallel generation requests involving the same type of a model. This property is not used by any `ProofProvider` default implementation and should be used in the `ProofProvider.modelsSchedulersProvider` implementation to have an effect. Equals to `1` by default.
 * @property `generationLogsFilePath` if it is not specified, a temporary file will be used (`ProofProviderInternal` is responsible for its maintainance).
 * @property `debugLogs` enables debug logs for the internal `GenerationsLogger`.
 * @property `enableModelsSchedulingDebugLogs` enables debug logs for the internal models scheduler.
 */
export type ProofProviderParams = Partial<ResolvedProofProviderParams>;

export interface ResolvedProofProviderParams {
    readonly eventLogger: EventLogger | undefined;
    readonly errorsHandlingMode: ErrorsHandlingMode;
    readonly generationParallelism: number;
    readonly generationLogsFilePath: string | undefined;
    readonly debugLogs: boolean;
    readonly enableModelsSchedulingDebugLogs: boolean;
}

export function resolveProofProviderParamsWithDefaults(
    proofProviderParams: ProofProviderParams
): ResolvedProofProviderParams {
    return {
        eventLogger: proofProviderParams.eventLogger,
        errorsHandlingMode:
            proofProviderParams.errorsHandlingMode ??
            ErrorsHandlingMode.RETHROW_ERRORS,
        generationParallelism: proofProviderParams.generationParallelism ?? 1,
        generationLogsFilePath:
            proofProviderParams.generationLogsFilePath ?? undefined,
        debugLogs: proofProviderParams.debugLogs ?? false,
        enableModelsSchedulingDebugLogs:
            proofProviderParams.enableModelsSchedulingDebugLogs ?? false,
    };
}
