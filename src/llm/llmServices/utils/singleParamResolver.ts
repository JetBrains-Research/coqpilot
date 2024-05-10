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
        valueBuilder: ValueBuilder<InputType, T>,
        helpMessageIfNotResolved?: string
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

interface Overrider<InputType, T> {
    valueBuilder: ValueBuilder<InputType, T>;
    explanationMessage?: string;
}

interface DefaultResolver<InputType, T> {
    valueBuilder: ValueBuilder<InputType, T>;
    noDefaultValueHelpMessage?: string;
}

class SingleParamResolverBuilderImpl<InputType, T>
    implements SingleParamResolverBuilder<InputType, T>
{
    private overrider: Overrider<InputType, T> | undefined = undefined;
    constructor(private readonly inputParamName: string) {}

    override(
        valueBuilder: ValueBuilder<InputType, T>,
        paramMessage: string
    ): SingleParamResolverBuilder<InputType, T> {
        if (this.overrider !== undefined) {
            throw new Error(
                `parameter \'${this.inputParamName}\'is overriden multiple times`
            );
        }
        this.overrider = {
            valueBuilder: valueBuilder,
            explanationMessage: paramMessage,
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
        valueBuilder: ValueBuilder<InputType, T>,
        noDefaultValueHelpMessage?: string
    ): SingleParamWithValueResolverBuilder<InputType, T> {
        return new SingleParamWithValueResolverBuilderImpl(
            this.inputParamName,
            this.overrider,
            {
                valueBuilder: valueBuilder,
                noDefaultValueHelpMessage: noDefaultValueHelpMessage,
            }
        );
    }

    requiredToBeConfigured(): SingleParamWithValueResolverBuilder<
        InputType,
        T
    > {
        return new SingleParamWithValueResolverBuilderImpl(
            this.inputParamName,
            this.overrider,
            undefined
        );
    }
}

class SingleParamWithValueResolverBuilderImpl<InputType, T>
    implements SingleParamWithValueResolverBuilder<InputType, T>
{
    constructor(
        private readonly inputParamName: string,
        private readonly overrider?: Overrider<InputType, T>,
        private readonly defaultResolver?: DefaultResolver<InputType, T>
    ) {}

    validate(
        ...validationRules: ValidationRule<T>[]
    ): SingleParamResolver<InputType, T> {
        return new SingleParamResolverImpl(
            this.inputParamName,
            this.overrider,
            this.defaultResolver,
            validationRules
        );
    }

    noValidationNeeded(): SingleParamResolver<InputType, T> {
        return new SingleParamResolverImpl(
            this.inputParamName,
            this.overrider,
            this.defaultResolver,
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
        private readonly overrider?: Overrider<InputType, T>,
        private readonly defaultResolver?: DefaultResolver<InputType, T>,
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
                result.isInvalidCause = `"${this.quotedName()} is configured with the "${userValue}" value of the wrong type"`;
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
        if (this.overrider !== undefined) {
            const { valueBuilder, explanationMessage } = this.overrider;
            value = valueBuilder(inputParams);
            if (this.overridenWithMockValue) {
                // no checks and logs are needed, just return value
                result.resultValue = value;
                return result;
            }
            result.overriden = {
                wasPerformed: true,
                withValue: value,
                message: explanationMessage,
            };
        }

        // if user value is still undefined after overriden resolution,
        // resolve with default
        if (value === undefined && this.defaultResolver !== undefined) {
            const { valueBuilder, noDefaultValueHelpMessage } =
                this.defaultResolver;
            value = valueBuilder(inputParams);
            result.resolvedWithDefault = {
                wasPerformed: true,
                withValue: value,
            };
            // failed to resolve value because default value was not found (but could potentially)
            if (value === undefined) {
                result.isInvalidCause = `"${this.noValueMessage}. ${noDefaultValueHelpMessage}."`;
                return result;
            }
        }

        // failed to resolve value
        if (value === undefined) {
            result.isInvalidCause = this.noValueMessage();
            return result;
        }

        // validate result value
        for (const [validateValue, paramShouldMessage] of this
            .validationRules) {
            const validationResult = validateValue(value);
            if (!validationResult) {
                result.isInvalidCause = `${this.quotedName()} should ${paramShouldMessage}, but has value "${value}"`;
                return result;
            }
        }

        result.resultValue = value;
        return result;
    }

    private quotedName(): string {
        return `\`${this.inputParamName}\``;
    }

    private noValueMessage(): string {
        return `"${this.quotedName} is required, but neither a user value nor a default one is specified"`;
    }
}
