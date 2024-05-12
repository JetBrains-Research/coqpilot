export function resolveParam<InputType, T>(
    inputParamName: string
): SingleParamResolverBuilder<InputType, T> {
    return new SingleParamResolverBuilderImpl(inputParamName);
}

export function insertParam<InputType, T>(
    valueBuilder: StrictValueBuilder<InputType, T>
): SingleParamWithValueResolverBuilder<InputType, T> {
    return new SingleParamWithValueResolverBuilderImpl(
        undefined,
        { valueBuilder: valueBuilder },
        undefined
    );
}

// Note: undefined should be returned iff this step is skipped at resolution
export type ValueBuilder<InputType, T> = (
    inputParams: InputType
) => T | undefined;
export type StrictValueBuilder<InputType, T> = (inputParams: InputType) => T;

export type ValidationRule<InputType, T> = [Validator<InputType, T>, string];
export type Validator<InputType, T> = (
    value: T,
    inputParams: InputType
) => boolean;

export interface SingleParamResolverBuilder<InputType, T> {
    override(
        valueBuilder: ValueBuilder<InputType, T>,
        paramMessage?: string
    ): SingleParamResolverBuilder<InputType, T>;

    overrideWithMock(
        valueBuilder: StrictValueBuilder<InputType, T>
    ): SingleParamResolver<InputType, T>;

    default(
        valueBuilder: ValueBuilder<InputType, T>,
        helpMessageIfNotResolved?: string
    ): SingleParamWithValueResolverBuilder<InputType, T>;

    requiredToBeConfigured(): SingleParamWithValueResolverBuilder<InputType, T>;
}

export interface SingleParamWithValueResolverBuilder<InputType, T> {
    validate(
        ...validationRules: ValidationRule<InputType, T>[]
    ): SingleParamResolver<InputType, T>;

    noValidationNeeded(): SingleParamResolver<InputType, T>;

    validateAtRuntimeOnly(): SingleParamResolver<InputType, T>;
}

export interface SingleParamResolver<InputType, T> {
    resolve(inputParams: InputType): SingleParamResolutionResult<T>;
}

export interface SingleParamResolutionResult<T> {
    inputParamName?: string;
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
        paramMessage?: string
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
        valueBuilder: StrictValueBuilder<InputType, T>
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
        private readonly inputParamName?: string,
        private readonly overrider?: Overrider<InputType, T>,
        private readonly defaultResolver?: DefaultResolver<InputType, T>
    ) {}

    validate(
        ...validationRules: ValidationRule<InputType, T>[]
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
        private readonly inputParamName?: string,
        private readonly overrider?: Overrider<InputType, T>,
        private readonly defaultResolver?: DefaultResolver<InputType, T>,
        private readonly validationRules: ValidationRule<InputType, T>[] = [],
        private readonly overridenWithMockValue: boolean = false
    ) {}

    // Note: unfortunately, the language does not allow to validate the type of the parameter properly
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

        let value: T | undefined = undefined;
        let resultIsComplete = false;

        [value, resultIsComplete] = this.tryToReadInputValue(
            inputParams,
            result
        );
        if (resultIsComplete) {
            return result;
        }

        [value, resultIsComplete] = this.tryToResolveWithOverrider(
            inputParams,
            result,
            value
        );
        if (resultIsComplete) {
            return result;
        }

        [value, resultIsComplete] = this.tryToResolveWithDefault(
            inputParams,
            result,
            value
        );
        if (resultIsComplete) {
            return result;
        }

        // failed to resolve value
        if (value === undefined) {
            result.isInvalidCause = this.noValueMessage();
            return result;
        }

        const valueIsValid = this.validateDefinedValue(
            inputParams,
            result,
            value
        );
        if (!valueIsValid) {
            return result;
        }

        result.resultValue = value;
        return result;
    }

    // returns true if `result` is already complete, false otherwise
    private tryToReadInputValue(
        inputParams: InputType,
        result: SingleParamResolutionResult<T>
    ): [T | undefined, boolean] {
        if (this.inputParamName === undefined) {
            return [undefined, false];
        }
        const userValue = this.accessParamByName(
            inputParams,
            this.inputParamName
        );
        if (userValue === undefined) {
            return [undefined, false];
        }
        // if user specified value, then take it
        const userValueAsT = userValue as T;
        if (userValueAsT !== null) {
            result.inputReadCorrectly = {
                wasPerformed: true,
                withValue: userValueAsT,
            };
            return [userValueAsT, false];
        } else {
            // unfortunately, this case is unreachable: TypeScript does not provide the way to check that `userValue` is of `T` type indeed
            throw Error(
                `cast of \`any\` to generic \`T\` type should always succeed, value = "${userValue}" for ${this.quotedName()} parameter`
            );
        }
    }

    private accessParamByName(
        inputParams: InputType,
        inputParamNameInDotNotation: string
    ): any {
        const propertiesNames = inputParamNameInDotNotation.split(".");
        let accessedProperty: any = inputParams;
        for (const propertyName of propertiesNames) {
            const accessKey = propertyName as keyof typeof accessedProperty;
            if (
                accessedProperty === undefined ||
                accessedProperty === null ||
                accessKey === null
            ) {
                throw Error(
                    `resolver of ${this.quotedName()} is configured incorrectly: failed to access this property in "${JSON.stringify(inputParams)}" input params`
                );
            }
            accessedProperty = accessedProperty[accessKey];
        }
        return accessedProperty;
    }

    // override value (it could be overriden with undefined, so as to force resolution with default)
    // returns true if `result` is already complete, false otherwise
    private tryToResolveWithOverrider(
        inputParams: InputType,
        result: SingleParamResolutionResult<T>,
        value: T | undefined
    ): [T | undefined, boolean] {
        if (this.overrider === undefined) {
            return [value, false];
        }
        const { valueBuilder, explanationMessage } = this.overrider;
        const valueToOverrideWith = valueBuilder(inputParams);
        if (this.overridenWithMockValue) {
            // no checks and logs are needed, just return value
            result.resultValue = valueToOverrideWith;
            if (valueToOverrideWith === undefined) {
                throw Error(
                    `${this.quotedName()} is expected to be a mock value, but its builder resolved with "undefined"`
                );
            }
            return [valueToOverrideWith, true];
        }
        result.overriden = {
            wasPerformed: true,
            withValue: valueToOverrideWith,
            message: explanationMessage,
        };
        return [valueToOverrideWith, false];
    }

    // returns true if `result` is already complete, false otherwise
    private tryToResolveWithDefault(
        inputParams: InputType,
        result: SingleParamResolutionResult<T>,
        value: T | undefined
    ): [T | undefined, boolean] {
        // if user value is still undefined after overriden resolution,
        // resolve with default
        if (value !== undefined || this.defaultResolver === undefined) {
            return [value, false];
        }
        const { valueBuilder, noDefaultValueHelpMessage } =
            this.defaultResolver;
        value = valueBuilder(inputParams);
        result.resolvedWithDefault = {
            wasPerformed: true,
            withValue: value,
        };
        // failed to resolve value because default value was not found (but could potentially)
        if (value === undefined) {
            result.isInvalidCause = `${this.noValueMessage()}. ${noDefaultValueHelpMessage}`;
            return [value, true];
        }
        return [value, false];
    }

    // returns true if value is valid, false otherwise
    private validateDefinedValue(
        inputParams: InputType,
        result: SingleParamResolutionResult<T>,
        value: T
    ): boolean {
        for (const [validateValue, paramShouldMessage] of this
            .validationRules) {
            const validationResult = validateValue(value, inputParams);
            if (!validationResult) {
                result.isInvalidCause = `${this.quotedName()} should ${paramShouldMessage}, but has value "${JSON.stringify(value)}"`;
                return false;
            }
        }
        return true;
    }

    private quotedName(): string {
        return `\`${this.inputParamName}\``;
    }

    private noValueMessage(): string {
        return `"${this.quotedName()} is required, but neither a user value nor a default one is specified"`;
    }
}
