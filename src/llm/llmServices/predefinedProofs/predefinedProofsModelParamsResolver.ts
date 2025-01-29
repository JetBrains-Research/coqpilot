import { PredefinedProofsUserModelParams } from "../../userModelParams";
import {
    MultiroundProfile,
    PredefinedProofsModelParams,
    predefinedProofsModelParamsSchema,
} from "../modelParams";
import { BasicModelParamsResolver } from "../utils/paramsResolvers/basicModelParamsResolvers";
import { ValidParamsResolverImpl } from "../utils/paramsResolvers/paramsResolverImpl";

export class PredefinedProofsModelParamsResolver
    extends BasicModelParamsResolver<
        PredefinedProofsUserModelParams,
        PredefinedProofsModelParams
    >
    implements
        ValidParamsResolverImpl<
            PredefinedProofsUserModelParams,
            PredefinedProofsModelParams
        >
{
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
    ).overrideWithMock((inputParams) =>
        Math.max(0, ...inputParams.tactics.map((tactic) => tactic.length))
    );

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

    readonly defaultChoices = this.resolveParam<number>("choices")
        .override(
            (inputParams) => inputParams.tactics.length,
            `always equals to the total number of \`tactics\``
        )
        .requiredToBeConfigured()
        .validate(
            [(value) => value >= 0, "be non-negative"],
            [
                (value, inputParams) => value <= inputParams.tactics.length,
                (inputParams) =>
                    `be less than or equal to the total number of \`tactics\` (${inputParams.tactics.length} for the specified \`tactics\`)`,
            ]
        );
}
