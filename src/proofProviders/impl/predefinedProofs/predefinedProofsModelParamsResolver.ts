import { PredefinedProofsUserModelParams } from "../../userModelParams";
import {
    PredefinedProofsModelParams,
    predefinedProofsModelParamsSchema,
} from "../modelParams";
import { DefaultNonChatBasedModelParamsResolver } from "../utils/paramsResolvers/kit/nonChatBasedModelParamsResolver";
import { ValidParamsResolverImpl } from "../utils/paramsResolvers/paramsResolverImpl";

export class PredefinedProofsModelParamsResolver
    extends DefaultNonChatBasedModelParamsResolver<
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

    readonly maxTokensToGenerate = this.resolveParam<number>(
        "maxTokensToGenerate"
    ).overrideWithMock((inputParams) =>
        Math.max(0, ...inputParams.tactics.map((tactic) => tactic.length))
    );

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
