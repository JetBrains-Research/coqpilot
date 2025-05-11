import { EventLogger } from "../../logging/eventLogger";

import { ErrorsHandlingMode } from "./commonStructures/errorsHandlingMode";

/**
 * @property `eventLogger` is used to send proof generation events. If not specified, event logging will be disabled.
 * @proptery `errorsHandlingMode` defines how errors during method calls are handled: whether they are rethrown or swallowed. Regardless of the mode, errors are logged. By default, `ErrorsHandlingMode.RETHROW_ERRORS`.
 * @property `generationParallelism` defines max number of parallel generation requests involving the same type of a model. This property is not used by any `LLMService` default implementation and should be used in the `LLMServiceImpl.modelsSchedulersProvider` implementation to have an effect. Equals to `1` by default.
 * @property `generationLogsFilePath` if it is not specified, a temporary file will be used (`LLMServiceInternal` is responsible for its maintainance).
 * @property `debugLogs` enables debug logs for the internal `GenerationsLogger`.
 * @property `enableModelsSchedulingDebugLogs` enables debug logs for the internal models scheduler.
 */
export type LLMServiceParams = Partial<ResolvedLLMServiceParams>;

export interface ResolvedLLMServiceParams {
    readonly eventLogger: EventLogger | undefined;
    readonly errorsHandlingMode: ErrorsHandlingMode;
    readonly generationParallelism: number;
    readonly generationLogsFilePath: string | undefined;
    readonly debugLogs: boolean;
    readonly enableModelsSchedulingDebugLogs: boolean;
}

export function resolveServiceParamsWithDefaults(
    serviceParams: LLMServiceParams
): ResolvedLLMServiceParams {
    return {
        eventLogger: serviceParams.eventLogger,
        errorsHandlingMode:
            serviceParams.errorsHandlingMode ??
            ErrorsHandlingMode.RETHROW_ERRORS,
        generationParallelism: serviceParams.generationParallelism ?? 1,
        generationLogsFilePath:
            serviceParams.generationLogsFilePath ?? undefined,
        debugLogs: serviceParams.debugLogs ?? false,
        enableModelsSchedulingDebugLogs:
            serviceParams.enableModelsSchedulingDebugLogs ?? false,
    };
}
