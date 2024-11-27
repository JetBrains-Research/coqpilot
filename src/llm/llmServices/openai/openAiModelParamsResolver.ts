import { OpenAiUserModelParams } from "../../userModelParams";
import { OpenAiModelParams, openAiModelParamsSchema } from "../modelParams";
import { BasicModelParamsResolver } from "../utils/paramsResolvers/basicModelParamsResolvers";
import { ValidationRules } from "../utils/paramsResolvers/builders";
import { ValidParamsResolverImpl } from "../utils/paramsResolvers/paramsResolverImpl";

export class OpenAiModelParamsResolver
    extends BasicModelParamsResolver<OpenAiUserModelParams, OpenAiModelParams>
    implements ValidParamsResolverImpl<OpenAiUserModelParams, OpenAiModelParams>
{
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

    readonly tokensLimit = this.resolveParam<number>("tokensLimit")
        .default((inputParams) =>
            OpenAiModelParamsResolver._modelToTokensLimit.get(
                inputParams.modelName
            )
        )
        .validate(ValidationRules.bePositiveNumber, [
            (value, inputParams) => {
                const actualTokensLimit =
                    OpenAiModelParamsResolver._modelToTokensLimit.get(
                        inputParams.modelName
                    );
                if (
                    actualTokensLimit === undefined ||
                    value <= actualTokensLimit
                ) {
                    return true;
                }
                return false;
            },
            (inputParams) =>
                `be not greater than the known tokens limit (${OpenAiModelParamsResolver._modelToTokensLimit.get(inputParams.modelName)}) for the "${inputParams.modelName}" model`,
        ]);

    /**
     * Since the actual maximum numbers of tokens that the models can generate are sometimes equal to their token limits,
     * a special algorithm to suggest a proper practical default value is used.
     * - If `actualTokensLimit` is twice or more times greater than `actualMaxTokensToGenerate`, return the actual value.
     * - Otherwise, return minimum of `actualTokensLimit` / 2 and 4096.
     *
     * Of course, if the model is unknown to the resolver, no default resolution will happen.
     */
    readonly maxTokensToGenerate = this.resolveParam<number>(
        "maxTokensToGenerate"
    )
        .default((inputParams) => {
            const actualMaxTokensToGenerate =
                OpenAiModelParamsResolver._modelToMaxTokensToGenerate.get(
                    inputParams.modelName
                );
            const actualTokensLimit =
                inputParams.tokensLimit ??
                OpenAiModelParamsResolver._modelToTokensLimit.get(
                    inputParams.modelName
                );
            if (
                actualMaxTokensToGenerate === undefined ||
                actualTokensLimit === undefined
            ) {
                return undefined;
            }
            if (2 * actualMaxTokensToGenerate < actualTokensLimit) {
                return actualMaxTokensToGenerate;
            }
            const halfTokensLimit = Math.floor(actualTokensLimit / 2);
            return Math.min(halfTokensLimit, 4096);
        })
        .validate(ValidationRules.bePositiveNumber, [
            (value, inputParams) => {
                const actualMaxTokensToGenerate =
                    OpenAiModelParamsResolver._modelToMaxTokensToGenerate.get(
                        inputParams.modelName
                    );
                if (
                    actualMaxTokensToGenerate === undefined ||
                    value <= actualMaxTokensToGenerate
                ) {
                    return true;
                }
                return false;
            },
            (inputParams) =>
                `be not greater than the known max tokens to generate limit (${OpenAiModelParamsResolver._modelToMaxTokensToGenerate.get(inputParams.modelName)}) for the "${inputParams.modelName}" model`,
        ]);

    /*
     * Default tokens parameters (both `_modelToTokensLimit` and `_modelToMaxTokensToGenerate`) values
     * are taken from the official OpenAI docs: https://platform.openai.com/docs/models.
     */

    static readonly _modelToTokensLimit: Map<string, number> = new Map([
        ["gpt-4o", 128_000],
        ["gpt-4o-2024-08-06", 128_000],
        ["gpt-4o-2024-05-13", 128_000],
        ["gpt-4o-mini", 128_000],
        ["gpt-4o-mini-2024-07-18", 128_000],
        ["gpt-4-turbo", 128_000],
        ["gpt-4-turbo-2024-04-09", 128_000],
        ["gpt-4-turbo-preview", 128_000],
        ["gpt-4-0125-preview", 128_000],
        ["gpt-4-1106-preview", 128_000],
        ["gpt-4", 8192],
        ["gpt-4-0613", 8192],
        ["gpt-4-0314", 8192],
        ["gpt-3.5-turbo-0125", 16_385],
        ["gpt-3.5-turbo", 16_385],
        ["gpt-3.5-turbo-1106", 16_385],
        ["gpt-3.5-turbo-instruct", 4096],
    ]);

    /**
     * These are the actual maximum numbers of tokens that these models can generate.
     * However, sometimes these values are equal to the corresponding tokens limits,
     * so it would be impractical to set `maxTokensToGenerate` to their values.
     * Thus, the default resolver should check this case and suggest smaller values if possible.
     */
    static readonly _modelToMaxTokensToGenerate: Map<string, number> = new Map([
        ["gpt-4o", 16_384],
        ["gpt-4o-2024-08-06", 16_384],
        ["gpt-4o-2024-05-13", 4096],
        ["gpt-4o-mini", 16_384],
        ["gpt-4o-mini-2024-07-18", 16_384],
        ["gpt-4-turbo", 4096],
        ["gpt-4-turbo-2024-04-09", 4096],
        ["gpt-4-turbo-preview", 4096],
        ["gpt-4-0125-preview", 4096],
        ["gpt-4-1106-preview", 4096],
        ["gpt-4", 8192],
        ["gpt-4-0613", 8192],
        ["gpt-4-0314", 8192],
        ["gpt-3.5-turbo-0125", 4096],
        ["gpt-3.5-turbo", 4096],
        ["gpt-3.5-turbo-1106", 4096],
        ["gpt-3.5-turbo-instruct", 4096],
    ]);
}
