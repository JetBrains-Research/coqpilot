import { DeepSeekUserModelParams } from "../../userModelParams";
import { DeepSeekModelParams, deepSeekModelParamsSchema } from "../modelParams";
import { BasicModelParamsResolver } from "../utils/paramsResolvers/basicModelParamsResolvers";
import { ValidParamsResolverImpl } from "../utils/paramsResolvers/paramsResolverImpl";

export class DeepSeekModelParamsResolver
    extends BasicModelParamsResolver<
        DeepSeekUserModelParams,
        DeepSeekModelParams
    >
    implements
        ValidParamsResolverImpl<DeepSeekUserModelParams, DeepSeekModelParams>
{
    constructor() {
        super(deepSeekModelParamsSchema, "DeepSeekModelParams");
    }

    readonly modelName = this.resolveParam<string>("modelName")
        .requiredToBeConfigured()
        .validate([
            (value) =>
                DeepSeekModelParamsResolver.allowedModels.includes(value),
            `be one of the allowed models: ${DeepSeekModelParamsResolver.allowedModels.join(
                ", "
            )}`,
        ]);

    readonly temperature = this.resolveParam<number>("temperature")
        .requiredToBeConfigured()
        .validate([
            (value) => value >= 0 && value <= 2,
            "be in range between 0 and 2",
        ]);

    readonly apiKey = this.resolveParam<string>("apiKey")
        .requiredToBeConfigured()
        .validateAtRuntimeOnly();

    static readonly allowedModels = ["deepseek-chat", "deepseek-reasoner"];
}
