import {
    GrazieUserModelParams,
    LMStudioUserModelParams,
    OpenAiUserModelParams,
    PredefinedProofsUserModelParams,
} from "../userModelParams";

import { GrazieService } from "./grazie/grazieService";
import {
    GrazieModelParams,
    LMStudioModelParams,
    MultiroundProfile,
    OpenAiModelParams,
    PredefinedProofsModelParams,
} from "./modelParams";
import { BasicModelParamsResolver } from "./utils/paramsResolver";

export class PredefinedProofsModelParamsResolver extends BasicModelParamsResolver<
    PredefinedProofsUserModelParams,
    PredefinedProofsModelParams
> {
    readonly tactics = this.resolveParam<string[]>("tactics")
        .requiredToBeConfigured()
        .validate([(value) => value.length > 0, "be not empty"]);

    readonly systemPrompt = this.resolveParam<string>(
        "systemPrompt"
    ).overrideWithMock((_) => "");

    readonly maxTokensToGenerate = this.resolveParam<number>(
        "maxTokensToGenerate"
    ).overrideWithMock((userModelParams) =>
        Math.max(0, ...userModelParams.tactics.map((tactic) => tactic.length))
    );

    readonly tokensLimit = this.resolveParam<number>(
        "tokensLimit"
    ).overrideWithMock((_) => Number.POSITIVE_INFINITY);

    readonly multiroundProfile = this.resolveParam<MultiroundProfile>(
        "multiroundProfile"
    ).overrideWithMock(() => {
        return {
            maxRoundsNumber: 1,
            proofFixChoices: 0,
            proofFixPrompt: "",
        };
    });
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
        .validate([(value) => value >= 0, "be positive"]);
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
            (_) => GrazieService.maxTokensToGeneratePredefined,
            `is always "${GrazieService.maxTokensToGeneratePredefined}" for \`GrazieService\``
        )
        .requiredToBeConfigured()
        .validate([(value) => value > 0, "be positive"]);

    readonly tokensLimit = this.resolveParam<number>("tokensLimit")
        .requiredToBeConfigured()
        .validate([(value) => value >= 0, "be positive"]);
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

    readonly maxTokensToGenerate = this.resolveParam<number>(
        "maxTokensToGenerate"
    )
        .requiredToBeConfigured()
        .validate([(value) => value > 0, "be positive"]);

    readonly tokensLimit = this.resolveParam<number>("tokensLimit")
        .requiredToBeConfigured()
        .validate([(value) => value >= 0, "be positive"]);
}
