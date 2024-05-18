import { PredefinedProofsUserModelParams } from "../../userModelParams";
import {
    MultiroundProfile,
    PredefinedProofsModelParams,
    predefinedProofsModelParamsSchema,
} from "../modelParams";
import { BasicModelParamsResolver } from "../utils/paramsResolvers/basicModelParamsResolvers";

export class PredefinedProofsModelParamsResolver extends BasicModelParamsResolver<
    PredefinedProofsUserModelParams,
    PredefinedProofsModelParams
> {
    constructor() {
        super(predefinedProofsModelParamsSchema, "PredefinedProofsModelParams");
    }

    readonly tactics = this.resolveParam<string[]>("tactics")
        .requiredToBeConfigured()
        .validate([(value) => value.length > 0, "be non-empty"]);

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
    ).overrideWithMock(() => Number.MAX_SAFE_INTEGER);

    readonly multiroundProfile = this.resolveParam<MultiroundProfile>(
        "multiroundProfile"
    ).overrideWithMock(() => {
        return {
            maxRoundsNumber: 1,
            defaultProofFixChoices: 0,
            proofFixPrompt: "",
        };
    });

    readonly defaultChoices = this.resolveParam<number>("choices")
        .override(
            (userModelParams) => userModelParams.tactics.length,
            `always equals to the total number of \`tactics\``
        )
        .requiredToBeConfigured()
        .validate(
            [(value) => value >= 0, "be non-negative"],
            [
                (value, userModelParams) =>
                    value <= userModelParams.tactics.length,
                "be less than or equal to the total number of `tactics`",
            ]
        );
}
