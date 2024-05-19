import { GrazieUserModelParams } from "../../userModelParams";
import { GrazieModelParams, grazieModelParamsSchema } from "../modelParams";
import { BasicModelParamsResolver } from "../utils/paramsResolvers/basicModelParamsResolvers";
import { ValidationRules } from "../utils/paramsResolvers/builders";

import { GrazieService } from "./grazieService";

export class GrazieModelParamsResolver extends BasicModelParamsResolver<
    GrazieUserModelParams,
    GrazieModelParams
> {
    constructor() {
        super(grazieModelParamsSchema, "GrazieModelParams");
    }

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
            `is always ${GrazieService.maxTokensToGeneratePredefined} for \`GrazieService\``
        )
        .requiredToBeConfigured()
        .validate(ValidationRules.bePositiveNumber);
}
