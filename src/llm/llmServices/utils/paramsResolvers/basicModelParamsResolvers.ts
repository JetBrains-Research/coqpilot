import {
    UserModelParams,
    UserMultiroundProfile,
} from "../../../userModelParams";
import {
    ModelParams,
    MultiroundProfile,
    multiroundProfileSchema,
} from "../../modelParams";

import { ValidationRules } from "./builders";
import {
    ParamsResolverImpl,
    ValidParamsResolverImpl,
} from "./paramsResolverImpl";

export class BasicMultiroundProfileResolver
    extends ParamsResolverImpl<UserMultiroundProfile, MultiroundProfile>
    implements ValidParamsResolverImpl<UserMultiroundProfile, MultiroundProfile>
{
    constructor() {
        super(multiroundProfileSchema, "MultiroundProfile");
    }

    readonly maxRoundsNumber = this.resolveParam<number>("maxRoundsNumber")
        .default(() => defaultMultiroundProfile.maxRoundsNumber)
        .validate(ValidationRules.bePositiveNumber);

    readonly defaultProofFixChoices = this.resolveParam<number>(
        "proofFixChoices"
    )
        .default(() => defaultMultiroundProfile.defaultProofFixChoices)
        .validate(ValidationRules.bePositiveNumber);

    readonly proofFixPrompt = this.resolveParam<string>("proofFixPrompt")
        .default(() => defaultMultiroundProfile.proofFixPrompt)
        .noValidationNeeded();

    readonly maxPreviousProofVersionsNumber = this.resolveParam<number>(
        "maxPreviousProofVersionsNumber"
    )
        .default(() => defaultMultiroundProfile.maxPreviousProofVersionsNumber)
        .validate(ValidationRules.beNonNegativeNumber);
}

/**
 * Properties of `defaultMultiroundProfile` can be used separately.
 * - Multiround is disabled by default.
 * - 1 fix version per proof by default.
 * - Default `proofFixPrompt` includes `${diagnostic}` message.
 * - The default maximum number of the latest proof versions is not limited.
 */
export const defaultMultiroundProfile: MultiroundProfile = {
    maxRoundsNumber: 1,
    defaultProofFixChoices: 1,
    proofFixPrompt:
        "Unfortunately, the last proof is not correct. Here is the compiler's feedback: `${diagnostic}`. Please, fix the proof.",
    maxPreviousProofVersionsNumber: Number.MAX_SAFE_INTEGER,
};

export class BasicModelParamsResolver<
        InputType extends UserModelParams,
        ResolveToType extends ModelParams,
    >
    extends ParamsResolverImpl<InputType, ResolveToType>
    implements ValidParamsResolverImpl<InputType, ModelParams>
{
    readonly modelId = this.resolveParam<string>("modelId")
        .requiredToBeConfigured()
        .noValidationNeeded();

    readonly systemPrompt = this.resolveParam<string>("systemPrompt")
        .default(() => defaultSystemMessageContent)
        .noValidationNeeded();

    readonly maxTokensToGenerate = this.resolveParam<number>(
        "maxTokensToGenerate"
    )
        .requiredToBeConfigured()
        .validate(ValidationRules.bePositiveNumber);

    readonly tokensLimit = this.resolveParam<number>("tokensLimit")
        .requiredToBeConfigured()
        .validate(ValidationRules.bePositiveNumber);

    readonly maxContextTheoremsNumber = this.resolveParam<number>(
        "maxContextTheoremsNumber"
    )
        .default(() => defaultMaxContextTheoremsNumber)
        .validate(ValidationRules.beNonNegativeNumber);

    readonly multiroundProfile = this.resolveNestedParams(
        "multiroundProfile",
        new BasicMultiroundProfileResolver()
    );

    readonly defaultChoices = this.resolveParam<number>("choices")
        .requiredToBeConfigured()
        .validate(ValidationRules.bePositiveNumber);
}

export const defaultSystemMessageContent =
    "Generate proof of the theorem from user input in Coq. You should only generate proofs in Coq. Never add special comments to the proof. Your answer should be a valid Coq proof. It should start with 'Proof.' and end with 'Qed.'.";

export const defaultMaxContextTheoremsNumber = Number.MAX_SAFE_INTEGER;
