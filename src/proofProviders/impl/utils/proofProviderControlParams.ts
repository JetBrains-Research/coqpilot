import { EventLogger } from "../../../logging/eventLogger";
import { Without } from "../../../utils/structures/typing";
import { ErrorsHandlingMode } from "../commonStructures/errorsHandlingMode";
import { ProofProviderParams } from "../proofProviderParams";

/**
 * Parameters that impact the logic behaviour of the `ProofProvider`.
 * Basically, some components (such as benchmarks), which need to control execution by themselves,
 * might not give full control of these parameters to the user.
 *
 * These parameters might be overriden by the controlling logic after being deserialized.
 */
export interface ProofProviderControlParams {
    readonly eventLogger: EventLogger | undefined;
    readonly errorsHandlingMode: ErrorsHandlingMode;
}

/**
 * Parameters that does not impact the logic behaviour of the `ProofProvider`.
 *
 * This parameters are the main target to (de)serialization.
 */
export type ProofProviderCustomizationParams<
    ProofProviderParamsType extends ProofProviderParams,
> = Without<ProofProviderParamsType, ProofProviderControlParams>;

export type BasicProofProviderCustomizationParams =
    ProofProviderCustomizationParams<ProofProviderParams>;
