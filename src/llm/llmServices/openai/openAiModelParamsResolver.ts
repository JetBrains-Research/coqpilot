import { OpenAiUserModelParams } from "../../userModelParams";
import { OpenAiModelParams, openAiModelParamsSchema } from "../modelParams";
import { BasicModelParamsResolver } from "../utils/paramsResolvers/basicModelParamsResolvers";
import { ValidationRules } from "../utils/paramsResolvers/builders";

export class OpenAiModelParamsResolver extends BasicModelParamsResolver<
    OpenAiUserModelParams,
    OpenAiModelParams
> {
    constructor() {
        super(openAiModelParamsSchema, "OpenAiModelParams");
    }

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
        .validate(ValidationRules.bePositiveNumber);

    readonly tokensLimit = this.resolveParam<number>("tokensLimit")
        .requiredToBeConfigured() // TODO
        .validate(ValidationRules.bePositiveNumber);
}
