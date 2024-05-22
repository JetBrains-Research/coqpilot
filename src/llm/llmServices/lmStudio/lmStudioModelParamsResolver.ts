import { LMStudioUserModelParams } from "../../userModelParams";
import { LMStudioModelParams, lmStudioModelParamsSchema } from "../modelParams";
import { BasicModelParamsResolver } from "../utils/paramsResolvers/basicModelParamsResolvers";
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
        .validate([
            (value) => value >= 0 && value <= 65535,
            "be a valid port value, i.e. in range between 0 and 65535",
        ]);
}
