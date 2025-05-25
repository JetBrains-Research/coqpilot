import { LMStudioUserModelParams } from "../../userModelParams";
import { LMStudioModelParams, lmStudioModelParamsSchema } from "../modelParams";
import { ValidationRules } from "../utils/paramsResolvers/builders";
import { BasicModelParamsResolver } from "../utils/paramsResolvers/kit/basicModelParamsResolvers";
import { ValidParamsResolverImpl } from "../utils/paramsResolvers/paramsResolverImpl";

export class LMStudioModelParamsResolver
    extends BasicModelParamsResolver<
        LMStudioUserModelParams,
        LMStudioModelParams
    >
    implements
        ValidParamsResolverImpl<LMStudioUserModelParams, LMStudioModelParams>
{
    constructor() {
        super(lmStudioModelParamsSchema, "LMStudioModelParams");
    }

    readonly temperature = this.resolveParam<number>("temperature")
        .requiredToBeConfigured()
        .validateAtRuntimeOnly();

    readonly port = this.resolveParam<number>("port")
        .requiredToBeConfigured()
        .validate(ValidationRules.beValidPortNumber);
}
