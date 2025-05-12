import { EventLogger } from "../../../logging/eventLogger";
import { Without } from "../../../utils/structures/typing";
import { ErrorsHandlingMode } from "../commonStructures/errorsHandlingMode";
import { LLMServiceParams } from "../llmServiceParams";

/**
 * Parameters that impact the logic behaviour of the `LLMService`.
 * Basically, some components (such as benchmarks), which need to control execution by themselves,
 * might not give full control of these parameters to the user.
 *
 * These parameters might be overriden by the controlling logic after being deserialized.
 */
export interface LLMServiceControlParams {
    readonly eventLogger: EventLogger | undefined;
    readonly errorsHandlingMode: ErrorsHandlingMode;
}

/**
 * Parameters that does not impact the logic behaviour of the `LLMService`.
 *
 * This parameters are the main target to (de)serialization.
 */
export type LLMServiceCustomizationParams<
    ServiceParams extends LLMServiceParams,
> = Without<ServiceParams, LLMServiceControlParams>;
