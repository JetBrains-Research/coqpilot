import {
    GrazieUserModelParams,
    LMStudioUserModelParams,
    OpenAiUserModelParams,
    PredefinedProofsUserModelParams,
    UserModelParams,
} from "../userModelParams";

import { GrazieService } from "./grazie/grazieService";
import {
    GrazieModelParams,
    LMStudioModelParams,
    ModelParams,
    MultiroundProfile,
    OpenAiModelParams,
    PredefinedProofsModelParams,
} from "./modelParams";
import { ParamsResolver } from "./utils/paramsResolver";

export class BasicModelParamsResolver<
    InputType extends UserModelParams,
    ResolveToType extends ModelParams,
> extends ParamsResolver<InputType, ResolveToType> {
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
        .validate([(value) => value > 0, "be positive"]);

    readonly tokensLimit = this.resolveParam<number>("tokensLimit")
        .requiredToBeConfigured()
        .validate([(value) => value >= 0, "be positive"]);

    readonly multiroundProfile = this.resolveParam<MultiroundProfile>(
        "multiroundProfile"
    )
        .default((userModelParams) => {
            const userMultiroundProfile = userModelParams.multiroundProfile;
            return {
                maxRoundsNumber:
                    userMultiroundProfile?.maxRoundsNumber ??
                    defaultMultiroundProfile.maxRoundsNumber,
                defaultProofFixChoices:
                    userMultiroundProfile?.proofFixChoices ??
                    defaultMultiroundProfile.defaultProofFixChoices,
                proofFixPrompt:
                    userMultiroundProfile?.proofFixPrompt ??
                    defaultMultiroundProfile.proofFixPrompt,
            };
        })
        .validate(
            [(profile) => profile.maxRoundsNumber > 0, "be positive"],
            [(profile) => profile.defaultProofFixChoices > 0, "be positive"]
        );

    readonly defaultChoices = this.resolveParam<number>("choices")
        .requiredToBeConfigured()
        .validate([(value) => value > 0, "be positive"]);
}

export const defaultSystemMessageContent: string =
    "Generate proof of the theorem from user input in Coq. You should only generate proofs in Coq. Never add special comments to the proof. Your answer should be a valid Coq proof. It should start with 'Proof.' and end with 'Qed.'.";

/**
 * Properties of `defaultMultiroundProfile` can be used separately.
 * - Multiround is disabled by default.
 * - 1 fix version per proof by default.
 * - Default `proofFixPrompt` includes `${diagnostic}` message.
 */
export const defaultMultiroundProfile: MultiroundProfile = {
    maxRoundsNumber: 1,
    defaultProofFixChoices: 1,
    proofFixPrompt:
        "Unfortunately, the last proof is not correct. Here is the compiler's feedback: `${diagnostic}`. Please, fix the proof.",
};

export class PredefinedProofsModelParamsResolver extends BasicModelParamsResolver<
    PredefinedProofsUserModelParams,
    PredefinedProofsModelParams
> {
    readonly tactics = this.resolveParam<string[]>("tactics")
        .requiredToBeConfigured()
        .validate([(value) => value.length > 0, "be not empty"]);

    readonly systemPrompt = this.resolveParam<string>(
        "systemPrompt"
    ).overrideWithMock(() => "");

    readonly maxTokensToGenerate = this.resolveParam<number>(
        "maxTokensToGenerate"
    ).overrideWithMock((userModelParams) =>
        Math.max(0, ...userModelParams.tactics.map((tactic) => tactic.length))
    );

    readonly tokensLimit = this.resolveParam<number>(
        "tokensLimit"
    ).overrideWithMock(() => Number.POSITIVE_INFINITY);

    readonly multiroundProfile = this.resolveParam<MultiroundProfile>(
        "multiroundProfile"
    ).overrideWithMock(() => {
        return {
            maxRoundsNumber: 1,
            defaultProofFixChoices: 0,
            proofFixPrompt: "",
        };
    });

    readonly defaultChoices = this.resolveParam<number>("defaultChoices")
        .override(
            (userModelParams) => userModelParams.tactics.length,
            `always equals to the total number of \`tactics\``
        )
        .requiredToBeConfigured()
        .validate(
            [(value) => value > 0, "be positive"],
            [
                (value, userModelParams) =>
                    value <= userModelParams.tactics.length,
                "be less than or equal to the total number of `tactics`",
            ]
        );
}

export class OpenAiModelParamsResolver extends BasicModelParamsResolver<
    OpenAiUserModelParams,
    OpenAiModelParams
> {
    readonly modelName = this.resolveParam<string>("modelName")
        .requiredToBeConfigured()
        .validateAtRuntimeOnly();

    readonly temperature = this.resolveParam<number>("temperature")
        .requiredToBeConfigured()
        .validate([
            (value) => value >= 0 && value <= 2,
            "be in range between 0 and 2",
        ]);

    readonly apiKey = this.resolveParam<string>("apiKey")
        .requiredToBeConfigured()
        .validateAtRuntimeOnly();

    readonly maxTokensToGenerate = this.resolveParam<number>(
        "maxTokensToGenerate"
    )
        .requiredToBeConfigured() // TODO
        .validate([(value) => value > 0, "be positive"]);

    readonly tokensLimit = this.resolveParam<number>("tokensLimit")
        .requiredToBeConfigured() // TODO
        .validate([(value) => value > 0, "be positive"]);
}

export class GrazieModelParamsResolver extends BasicModelParamsResolver<
    GrazieUserModelParams,
    GrazieModelParams
> {
    readonly modelName = this.resolveParam<string>("modelName")
        .requiredToBeConfigured()
        .validateAtRuntimeOnly();

    readonly apiKey = this.resolveParam<string>("apiKey")
        .requiredToBeConfigured()
        .validateAtRuntimeOnly();

    readonly maxTokensToGenerate = this.resolveParam<number>(
        "maxTokensToGenerate"
    )
        .override(
            () => GrazieService.maxTokensToGeneratePredefined,
            `is always "${GrazieService.maxTokensToGeneratePredefined}" for \`GrazieService\``
        )
        .requiredToBeConfigured()
        .validate([(value) => value > 0, "be positive"]);
}

export class LMStudioModelParamsResolver extends BasicModelParamsResolver<
    LMStudioUserModelParams,
    LMStudioModelParams
> {
    readonly modelName = this.resolveParam<string>("modelName")
        .requiredToBeConfigured()
        .validateAtRuntimeOnly();

    readonly temperature = this.resolveParam<number>("temperature")
        .requiredToBeConfigured()
        .validateAtRuntimeOnly();

    readonly port = this.resolveParam<number>("port")
        .requiredToBeConfigured()
        .validate([
            (value) => value >= 0 && value <= 65535,
            "be a valid port value, i.e. in range between 0 and 65535",
        ]);
}
