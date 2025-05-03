import { UserModelParams } from "../../../../userModelParams";
import { ModelParams, MultiroundProfile } from "../../../modelParams";

import { BasicModelParamsResolver } from "./basicModelParamsResolvers";

export class DefaultNonChatBasedModelParamsResolver<
    InputType extends UserModelParams,
    ResolveToType extends ModelParams,
> extends BasicModelParamsResolver<InputType, ResolveToType> {
    readonly systemPrompt = this.resolveParam<string>(
        "systemPrompt"
    ).overrideWithMock(() => "");

    readonly maxTokensToGenerate = this.resolveParam<number>(
        "maxTokensToGenerate"
    ).overrideWithMock(() => Number.MAX_SAFE_INTEGER);

    readonly tokensLimit = this.resolveParam<number>(
        "tokensLimit"
    ).overrideWithMock(() => Number.MAX_SAFE_INTEGER);

    readonly maxContextTheoremsNumber = this.resolveParam<number>(
        "maxContextTheoremsNumber"
    ).overrideWithMock(() => Number.MAX_SAFE_INTEGER);

    readonly multiroundProfile = this.resolveParam<MultiroundProfile>(
        "multiroundProfile"
    ).overrideWithMock(() => {
        return {
            maxRoundsNumber: 1,
            defaultProofFixChoices: 0,
            proofFixPrompt: "",
            maxPreviousProofVersionsNumber: 0,
        };
    });
}
