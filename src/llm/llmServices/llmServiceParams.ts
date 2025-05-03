import { EventLogger } from "../../logging/eventLogger";

import { ErrorsHandlingMode } from "./commonStructures/errorsHandlingMode";

export type LLMServiceParams = Partial<ResolvedLLMServiceParams>;

export interface ResolvedLLMServiceParams {
    eventLogger: EventLogger | undefined;
    errorsHandlingMode: ErrorsHandlingMode;
    generationLogsFilePath: string | undefined;
    debugLogs: boolean;
}

export function resolveServiceParamsWithDefaults(
    serviceParams: LLMServiceParams
): ResolvedLLMServiceParams {
    return {
        eventLogger: serviceParams.eventLogger,
        errorsHandlingMode:
            serviceParams.errorsHandlingMode ??
            ErrorsHandlingMode.RETHROW_ERRORS,
        generationLogsFilePath:
            serviceParams.generationLogsFilePath ?? undefined,
        debugLogs: serviceParams.debugLogs ?? false,
    };
}
