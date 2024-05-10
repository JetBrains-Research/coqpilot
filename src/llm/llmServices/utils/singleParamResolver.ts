export function resolveParam<InputType, T>(
    inputParamName: string
): SingleParamResolverBuilder<InputType, T> {
    return new SingleParamResolverBuilderImpl(inputParamName);
}

// Note: undefined should be returned iff this step is skipped at resolution
export type ValueBuilder<InputType, T> = (
    inputParams: InputType
) => T | undefined;

export type ValidationRule<T> = [(value: T) => boolean, string];

export interface SingleParamResolverBuilder<InputType, T> {
    override(
        valueBuilder: ValueBuilder<InputType, T>,
        paramMessage: string
    ): SingleParamResolverBuilder<InputType, T>;

    overrideWithMock(
        valueBuilder: ValueBuilder<InputType, T>
    ): SingleParamResolver<InputType, T>;

    default(
        valueBuilder: ValueBuilder<InputType, T>
    ): SingleParamWithValueResolverBuilder<InputType, T>;

    requiredToBeConfigured(): SingleParamWithValueResolverBuilder<InputType, T>;
}

export interface SingleParamWithValueResolverBuilder<InputType, T> {
    validate(
        ...validationRules: ValidationRule<T>[]
    ): SingleParamResolver<InputType, T>;

    noValidationNeeded(): SingleParamResolver<InputType, T>;

    validateAtRuntimeOnly(): SingleParamResolver<InputType, T>;
}

export interface SingleParamResolver<InputType, T> {
    resolve(inputParams: InputType): SingleParamResolutionResult<T>;
}

export interface SingleParamResolutionResult<T> {
    inputParamName: string;
    resultValue?: T;
    isInvalidCause?: string;
    inputReadCorrectly: ResolutionActionResult<T>;
    overriden: ResolutionActionDetailedResult<T>;
    resolvedWithDefault: ResolutionActionResult<T>;
}

export interface ResolutionActionResult<T> {
    wasPerformed: boolean;
    withValue?: T;
}

export interface ResolutionActionDetailedResult<T>
    extends ResolutionActionResult<T> {
    message?: string;
}

interface ValueBuilderWithMessage<InputType, T> {
    valueBuilder: ValueBuilder<InputType, T>;
    paramMessage?: string;
}

class SingleParamResolverBuilderImpl<InputType, T>
    implements SingleParamResolverBuilder<InputType, T>
{
    private overridenValueBuilderWithMessage:
        | ValueBuilderWithMessage<InputType, T>
        | undefined = undefined;
    constructor(private readonly inputParamName: string) {}

    override(
        valueBuilder: ValueBuilder<InputType, T>,
        paramMessage: string
    ): SingleParamResolverBuilder<InputType, T> {
        if (this.overridenValueBuilderWithMessage !== undefined) {
            throw new Error(
                `parameter \'${this.inputParamName}\'is overriden multiple times`
            );
        }
        this.overridenValueBuilderWithMessage = {
            valueBuilder: valueBuilder,
            paramMessage: paramMessage,
        };
        return this;
    }

    overrideWithMock(
        valueBuilder: ValueBuilder<InputType, T>
    ): SingleParamResolver<InputType, T> {
        return new SingleParamResolverImpl(
            this.inputParamName,
            {
                valueBuilder: valueBuilder,
            },
            undefined,
            [],
            true
        );
    }

    default(
        valueBuilder: ValueBuilder<InputType, T>
    ): SingleParamWithValueResolverBuilder<InputType, T> {
        return new SingleParamWithValueResolverBuilderImpl(
            this.inputParamName,
            this.overridenValueBuilderWithMessage,
            valueBuilder
        );
    }

    requiredToBeConfigured(): SingleParamWithValueResolverBuilder<
        InputType,
        T
    > {
        return new SingleParamWithValueResolverBuilderImpl(
            this.inputParamName,
            this.overridenValueBuilderWithMessage,
            undefined
        );
    }
}

class SingleParamWithValueResolverBuilderImpl<InputType, T>
    implements SingleParamWithValueResolverBuilder<InputType, T>
{
    constructor(
        private readonly inputParamName: string,
        private readonly overridenValueBuilderWithMessage?: ValueBuilderWithMessage<
            InputType,
            T
        >,
        private readonly defaultValueBuilder?: ValueBuilder<InputType, T>
    ) {}

    validate(
        ...validationRules: ValidationRule<T>[]
    ): SingleParamResolver<InputType, T> {
        return new SingleParamResolverImpl(
            this.inputParamName,
            this.overridenValueBuilderWithMessage,
            this.defaultValueBuilder,
            validationRules
        );
    }

    noValidationNeeded(): SingleParamResolver<InputType, T> {
        return new SingleParamResolverImpl(
            this.inputParamName,
            this.overridenValueBuilderWithMessage,
            this.defaultValueBuilder,
            []
        );
    }

    validateAtRuntimeOnly(): SingleParamResolver<InputType, T> {
        return this.noValidationNeeded();
    }
}

class SingleParamResolverImpl<InputType, T>
    implements SingleParamResolver<InputType, T>
{
    constructor(
        private readonly inputParamName: string,
        private readonly overridenValueBuilderWithMessage?: ValueBuilderWithMessage<
            InputType,
            T
        >,
        private readonly defaultValueBuilder?: ValueBuilder<InputType, T>,
        private readonly validationRules: ValidationRule<T>[] = [],
        private readonly overridenWithMockValue: boolean = false
    ) {}

    resolve(inputParams: InputType): SingleParamResolutionResult<T> {
        const result: SingleParamResolutionResult<T> = {
            inputParamName: this.inputParamName,
            resultValue: undefined,
            inputReadCorrectly: {
                wasPerformed: false,
            },
            overriden: {
                wasPerformed: false,
            },
            resolvedWithDefault: {
                wasPerformed: false,
            },
        };

        // read user's value
        const propertiesNames = this.inputParamName.split(".");
        let userValue: any = undefined;
        for (const propertyName of propertiesNames) {
            userValue = inputParams[propertyName as keyof typeof inputParams];
        }

        // if user specified value, then take it
        let value: T | undefined = undefined;
        if (userValue !== undefined) {
            const userValueAsT = userValue as T;
            if (userValueAsT === null) {
                result.isInvalidCause = `"\`${this.inputParamName}\` is configured with the "${userValue}" value of the wrong type"`;
                return result;
            } else {
                value = userValue;
                result.inputReadCorrectly = {
                    wasPerformed: true,
                    withValue: value,
                };
            }
        }

        // override value (it could be overriden with undefined, so as to force resolution with default)
        if (this.overridenValueBuilderWithMessage !== undefined) {
            const { valueBuilder, paramMessage } =
                this.overridenValueBuilderWithMessage;
            value = valueBuilder(inputParams);
            if (this.overridenWithMockValue) {
                // no checks and logs are needed, just return value
                result.resultValue = value;
                return result;
            }
            result.overriden = {
                wasPerformed: true,
                withValue: value,
                message: paramMessage,
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
            result.isInvalidCause = `"\`${this.inputParamName}\` is required, but neither a user value nor a default one is specified"`;
            return result;
        }

        // validate result value
        for (const [validateValue, paramShouldMessage] of this
            .validationRules) {
            const validationResult = validateValue(value);
            if (!validationResult) {
                result.isInvalidCause = `\`${this.inputParamName}\` should ${paramShouldMessage}, but has value "${value}"`;
                return result;
            }
        }

        result.resultValue = value;
        return result;
    }
}
