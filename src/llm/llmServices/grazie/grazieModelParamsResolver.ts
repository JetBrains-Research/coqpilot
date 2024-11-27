import { GrazieUserModelParams } from "../../userModelParams";
import { GrazieModelParams, grazieModelParamsSchema } from "../modelParams";
import { BasicModelParamsResolver } from "../utils/paramsResolvers/basicModelParamsResolvers";
import { ValidationRules } from "../utils/paramsResolvers/builders";
import { ValidParamsResolverImpl } from "../utils/paramsResolvers/paramsResolverImpl";

import { GrazieService } from "./grazieService";

export class GrazieModelParamsResolver
    extends BasicModelParamsResolver<GrazieUserModelParams, GrazieModelParams>
    implements ValidParamsResolverImpl<GrazieUserModelParams, GrazieModelParams>
{
    constructor() {
        super(grazieModelParamsSchema, "GrazieModelParams");
    }

    readonly modelName = this.resolveParam<string>("modelName")
        .requiredToBeConfigured()
        .validateAtRuntimeOnly();

    readonly apiKey = this.resolveParam<string>("apiKey")
        .requiredToBeConfigured()
        .validateAtRuntimeOnly();

    readonly authType = this.resolveParam<"stgn" | "prod">("authType")
        .requiredToBeConfigured()
        .validate([
            (value) => value === "stgn" || value === "prod",
            "be either 'stgn' or 'prod'",
        ]);

    readonly maxTokensToGenerate = this.resolveParam<number>(
        "maxTokensToGenerate"
    )
        .override(
            () => GrazieService.maxTokensToGeneratePredefined,
            `is always ${GrazieService.maxTokensToGeneratePredefined} for \`GrazieService\``
        )
        .requiredToBeConfigured()
        .validate(ValidationRules.bePositiveNumber);
}
