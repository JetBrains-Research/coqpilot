import { ConfigurationError } from "../llmServiceErrors";
import { OpenAiUserModelParams } from "../userModelParams";

import { MultiroundProfile, OpenAiModelParams } from "./modelParams";
import {
    defaultMultiroundProfile,
    defaultSystemMessageContent,
} from "./utils/defaultParametersResolver";

interface ParamResolver<InputType, T> {
    resolve(inputParams: InputType): ParamResolutionResult<T>;
}

// Note: undefined should be returned iff this step is skipped at resolution
type ValueBuilder<InputType, T> = (userModelParams: InputType) => T | undefined;

class BaseParamResolver<InputType, T> {
    constructor(
        private readonly paramName: string,
        private overridenValueBuilder?: ValueBuilder<InputType, T>
    ) {}

    override(
        valueBuilder: ValueBuilder<InputType, T>
    ): BaseParamResolver<InputType, T> {
        if (this.overridenValueBuilder !== undefined) {
            throw new Error(
                `parameter \'${this.paramName}\'is overriden multiple times`
            );
        }
        this.overridenValueBuilder = valueBuilder;
        return this;
    }

    overrideWithMock(
        valueBuilder: ValueBuilder<InputType, T>
    ): ParamWithValidatedValueResolver<InputType, T> {
        return new ParamWithValidatedValueResolver(
            this.paramName,
            valueBuilder,
            undefined,
            [],
            true
        );
    }

    default(
        valueBuilder: ValueBuilder<InputType, T>
    ): ParamWithValueResolver<InputType, T> {
        return new ParamWithValueResolver(
            this.paramName,
            this.overridenValueBuilder,
            valueBuilder
        );
    }

    required(): ParamWithValueResolver<InputType, T> {
        return new ParamWithValueResolver(
            this.paramName,
            this.overridenValueBuilder,
            undefined
        );
    }
}

type ValidationRule<T> = [(value: T) => boolean, string];

class ParamWithValueResolver<InputType, T> {
    constructor(
        private readonly paramName: string,
        private readonly overridenValueBuilder?: ValueBuilder<InputType, T>,
        private readonly defaultValueBuilder?: ValueBuilder<InputType, T>
    ) {}

    validate(
        ...validationRules: ValidationRule<T>[]
    ): ParamWithValidatedValueResolver<InputType, T> {
        return new ParamWithValidatedValueResolver(
            this.paramName,
            this.overridenValueBuilder,
            this.defaultValueBuilder,
            validationRules
        );
    }

    noValidation(): ParamWithValidatedValueResolver<InputType, T> {
        return new ParamWithValidatedValueResolver(
            this.paramName,
            this.overridenValueBuilder,
            this.defaultValueBuilder,
            []
        );
    }

    validateAtRuntime(): ParamWithValidatedValueResolver<InputType, T> {
        return this.noValidation();
    }
}

interface ParamResolutionActionResult<T> {
    wasPerformed: boolean;
    withValue?: T;
}

interface ParamResolutionResult<T> {
    overriden: ParamResolutionActionResult<T>;
    resolvedWithDefault: ParamResolutionActionResult<T>;
    isInvalidCause?: string;
    resultValue?: T;
}

class ParamWithValidatedValueResolver<InputType, T>
    implements ParamResolver<InputType, T>
{
    constructor(
        private readonly paramName: string,
        private readonly overridenValueBuilder?: ValueBuilder<InputType, T>,
        private readonly defaultValueBuilder?: ValueBuilder<InputType, T>,
        private readonly validationRules: ValidationRule<T>[] = [],
        private readonly overridenWithMockValue: boolean = false
    ) {}

    resolve(inputParams: InputType): ParamResolutionResult<T> {
        const result: ParamResolutionResult<T> = {
            overriden: {
                wasPerformed: false,
            },
            resolvedWithDefault: {
                wasPerformed: false,
            },
            resultValue: undefined,
        };

        // read user's value
        const propertiesNames = this.paramName.split(".");
        let userValue: any = undefined;
        for (const propertyName of propertiesNames) {
            userValue = inputParams[propertyName as keyof typeof inputParams];
        }

        // if user specified value, then take it
        let value: T | undefined = undefined;
        if (userValue !== undefined) {
            const userValueAsT = userValue as T;
            if (userValueAsT === null) {
                result.isInvalidCause = `"\`${this.paramName}\` is configured with the "${userValue}" value of the wrong type"`;
                return result;
            } else {
                value = userValue;
            }
        }

        // override value (it could be overriden with undefined, so as to force resolution with default)
        if (this.overridenValueBuilder !== undefined) {
            value = this.overridenValueBuilder(inputParams);
            if (this.overridenWithMockValue) {
                // no checks and logs are needed, just return value
                result.resultValue = value;
                return result;
            }
            result.overriden = {
                wasPerformed: true,
                withValue: value,
            };
        }

        // if user value is still undefined after overriden resolution,
        // resolve with default
        if (value === undefined && this.defaultValueBuilder !== undefined) {
            value = this.defaultValueBuilder(inputParams);
            result.resolvedWithDefault = {
                wasPerformed: true,
                withValue: value,
            };
        }

        // failed to resolve value
        if (value === undefined) {
            result.isInvalidCause = `"\`${this.paramName}\` is required, but neither a user value nor a default one is specified"`;
            return result;
        }

        // validate result value
        for (const [validateValue, paramShouldMessage] of this
            .validationRules) {
            const validationResult = validateValue(value);
            if (!validationResult) {
                result.isInvalidCause = `\`${this.paramName}\` should ${paramShouldMessage}, but has value "${value}"`;
                return result;
            }
        }

        result.resultValue = value;
        return result;
    }
}

interface ParamsResolutionResult<ResolveToType> {
    resolvedParams: ResolveToType;
}

// Notes:
// * every property should be of ParamWithValidatedValueResolver<*> type
// * how to specify properties names:
// - property's name should be equal to the one of ResolveToType properties
// - parameter's name in the ParamResolver should be a path to one of the properties of InputType
export class ParamsResolver<InputType, ResolveToType> {
    resolve(inputParams: InputType): ParamsResolutionResult<ResolveToType> {
        const resolvedParamsObject: { [key: string]: any } = {};
        for (const prop in this) {
            if (Object.prototype.hasOwnProperty.call(this, prop)) {
                const paramResolver = this[
                    prop
                ] as ParamWithValidatedValueResolver<InputType, any>;
                if (paramResolver === null) {
                    throw Error(
                        `\`ModelParamsResolver\` is configured incorrectly because of "${prop}": all properties should be built up to \`ParamWithValidatedValueResolver\` type`
                    );
                }
                const resolutionResult = paramResolver.resolve(inputParams);
                if (resolutionResult.isInvalidCause !== undefined) {
                    throw Error(`todo: ${resolutionResult.isInvalidCause}`); // TODO
                }
                resolvedParamsObject[prop] = resolutionResult.resultValue;
            }
        }
        const resolvedParams = resolvedParamsObject as ResolveToType;
        if (resolvedParams === null) {
            throw new ConfigurationError(
                `\`ModelParamsResolver\` is configured incorrectly: resulting "${JSON.stringify(resolvedParamsObject)}" could not be interpreted as \`ModelParams\` object`
            );
        }
        return {
            resolvedParams: resolvedParams,
        };
    }
}

export class OpenAiModelParamsResolver extends ParamsResolver<
    OpenAiUserModelParams,
    OpenAiModelParams
> {
    modelId = new BaseParamResolver<OpenAiUserModelParams, string>("modelId")
        .required()
        .noValidation();

    modelName = new BaseParamResolver<OpenAiUserModelParams, string>(
        "modelName"
    )
        .required()
        .validateAtRuntime(); // TODO

    temperature = new BaseParamResolver<OpenAiUserModelParams, number>(
        "temperature"
    )
        .required()
        .validate([
            (value) => value >= 0 && value <= 2,
            "be in range between 0 and 2",
        ]);

    apiKey = new BaseParamResolver<OpenAiUserModelParams, string>("apiKey")
        .required()
        .validateAtRuntime();

    systemPrompt = new BaseParamResolver<OpenAiUserModelParams, string>(
        "systemPrompt"
    )
        .default((_) => defaultSystemMessageContent)
        .noValidation();

    maxTokensToGenerate = new BaseParamResolver<OpenAiUserModelParams, number>(
        "maxTokensToGenerate"
    )
        .default((_) => undefined) // TODO
        .validate([(value) => value > 0, "be positive"]);

    tokensLimit = new BaseParamResolver<OpenAiUserModelParams, number>(
        "tokensLimit"
    )
        .default((_) => undefined) // TODO
        .validate([(value) => value >= 0, "be positive"]);

    multiroundProfile = new BaseParamResolver<
        OpenAiUserModelParams,
        MultiroundProfile
    >("multiroundProfile")
        .default((userModelParams) => {
            const userMultiroundProfile = userModelParams.multiroundProfile;
            return {
                maxRoundsNumber:
                    userMultiroundProfile?.maxRoundsNumber ??
                    defaultMultiroundProfile.maxRoundsNumber,
                proofFixChoices:
                    userMultiroundProfile?.proofFixChoices ??
                    defaultMultiroundProfile.proofFixChoices,
                proofFixPrompt:
                    userMultiroundProfile?.proofFixPrompt ??
                    defaultMultiroundProfile.proofFixPrompt,
            };
        })
        .validate(
            [(profile) => profile.maxRoundsNumber > 0, "be positive"],
            [(profile) => profile.proofFixChoices > 0, "be positive"]
        );
}
