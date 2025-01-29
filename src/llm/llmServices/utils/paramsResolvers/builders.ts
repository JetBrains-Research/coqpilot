import {
    stringifyAnyValue,
    stringifyDefinedValue,
} from "../../../../utils/printers";
import { illegalState, unreachable } from "../../../../utils/throwErrors";

import { AbstractSingleParamResolver, PropertyKey } from "./abstractResolvers";
import { SingleParamResolutionResult } from "./abstractResolvers";

/**
 * Facade function to create a single-parameter-resolver builder.
 * Then one can define the resolution of the `inputParamKey` property
 * of the input `InputType` object.
 */
export function resolveParam<InputType, T>(
    inputParamKey: PropertyKey<InputType>
): SingleParamResolverBuilder<InputType, T> {
    return new SingleParamResolverBuilderImpl(inputParamKey);
}

/**
 * Facade function to create a single-parameter-resolver builder.
 * Then one can define the resolution of the new property based on
 * the input `InputType` object.
 */
export function newParam<InputType, T>(
    valueBuilder: StrictValueBuilder<InputType, T>
): SingleParamWithValueResolverBuilder<InputType, T> {
    return new SingleParamWithValueResolverBuilderImpl(
        undefined,
        { valueBuilder: valueBuilder },
        undefined
    );
}

/**
 * First single-parameter-resolver builder interface.
 * It allows to define whether the parameter's value should be overriden,
 * resolved with default, or just required to be configured.
 */
export interface SingleParamResolverBuilder<InputType, T> {
    /**
     * Specifies that the parameter's value should be overriden.
     * Override actually happens only if the constructed value
     * differs from the input read one.
     *
     * Implementation notes:
     * - any conditions can be specified inside `valueBuilder`,
     *   so it is possible to make override conditional;
     * - `valueBuilder` can return undefined, forcing the following
     *   resolution with default.
     *
     * @param valueBuilder lambda to build the value to override with.
     * @param paramMessage optional message to explain the override to the user.
     */
    override(
        valueBuilder: ValueBuilder<InputType, T>,
        paramMessage?: Message<InputType>
    ): SingleParamResolverBuilder<InputType, T>;

    /**
     * Have the same functionality as `override` method,
     * but describes overriding with a mock value, i.e. the value
     * that will never be actually used. Thus, this override always succeeds
     * and cannot return undefined.
     *
     * Also, this override is never shown in logs (`overriden.wasPerformed` is false),
     * since mock resolutions should not be tracked the same as real once.
     * *TODO: support mock resolutions in logs with a separate property.*
     */
    overrideWithMock(
        valueBuilder: StrictValueBuilder<InputType, T>
    ): AbstractSingleParamResolver<InputType, T>;

    /**
     * Specifies that the parameter's value should be resolved with default if it is undefined.
     * Resolution with default is performed only if the previous steps result in the parameter's value
     * to be undefined (i.e. input was initially undefined and not overriden / was overriden with `undefined`).
     *
     * Implementation notes:
     * - any conditions can be specified inside `valueBuilder`,
     *   so it is possible to make resolution with default conditional;
     * - `valueBuilder` can return undefined, forcing the parameter's resolution to fail
     *   (since default resolution is the last step).
     *
     * @param valueBuilder lambda to build the default value.
     * @param helpMessageIfNotResolved optional message to show to the user if `valueBuilder` has not built a default value for the parameter (i.e. returned `undefined`).
     */
    default(
        valueBuilder: ValueBuilder<InputType, T>,
        helpMessageIfNotResolved?: Message<InputType>
    ): SingleParamWithValueResolverBuilder<InputType, T>;

    /**
     * Specifies that the parameter's value is required to be configured in the input `InputType` object,
     * i.e. does not have any value resolvers. Practically, this method just skips the step of specifying the value resolvers.
     */
    requiredToBeConfigured(): SingleParamWithValueResolverBuilder<InputType, T>;
}

/**
 * Second single-parameter-resolver builder interface.
 * It allows to define validation rules for the resolved parameter's value.
 */
export interface SingleParamWithValueResolverBuilder<InputType, T> {
    /**
     * Specifies validation rules to verify the resolved parameter's value with.
     * The rules will be checked in the order they appear in the arguments.
     */
    validate(
        ...validationRules: ValidationRule<InputType, T>[]
    ): AbstractSingleParamResolver<InputType, T>;

    /**
     * Specifies that the resolved parameter's value does not need validation.
     * Practically, this method just skips the step of specifying the validation rules.
     */
    noValidationNeeded(): AbstractSingleParamResolver<InputType, T>;

    /**
     * Specifies that the resolved parameter's value does need validation,
     * but it will be performed by the caller code at runtime only.
     * Practically, this method just skips the step of specifying the validation rules.
     */
    validateAtRuntimeOnly(): AbstractSingleParamResolver<InputType, T>;
}

/**
 * Builds the value to resolve the parameter with.
 * Return undefined value to skip the corresponding resolution step.
 */
export type ValueBuilder<InputType, T> = (
    inputParams: InputType
) => T | undefined;

/**
 * Builds the value to resolve the parameter with. Cannot return undefined values.
 */
export type StrictValueBuilder<InputType, T> = (inputParams: InputType) => T;

/**
 * Accepts `inputParams` and builds the message.
 */
export type MessageBuilder<InputType> = (inputParams: InputType) => string;

/**
 * Represents a message to use in the resolution logs. Can be both a simple string and
 * a builder, which builds the message from `inputParams`.
 */
export type Message<InputType> = string | MessageBuilder<InputType>;

function buildMessage<InputType>(
    message: Message<InputType> | undefined,
    inputParams: InputType
): string | undefined {
    return typeof message === "function" ? message(inputParams) : message;
}

/**
 * Specification of a single validation rule.
 * The first tuple element is a validator function, while the second one
 * is the message explaining the check. Generally, the message should be in such a format,
 * that the following phrase will make sense: `parameter's value should ${message}`.
 */
export type ValidationRule<InputType, T> = [
    Validator<InputType, T>,
    Message<InputType>,
];

/**
 * Predicate to validate the resolved parameter's value with.
 */
export type Validator<InputType, T> = (
    value: T,
    inputParams: InputType
) => boolean;

/**
 * Namespace that provides some common validation rules.
 */
export namespace ValidationRules {
    export const bePositiveNumber: ValidationRule<any, number> = [
        (value: number) => value > 0,
        "be positive",
    ];

    export const beNonNegativeNumber: ValidationRule<any, number> = [
        (value: number) => value >= 0,
        "be non-negative",
    ];
}

/**
 * Builders' implementation below >>>>>>>>>>>>>>>>>>>>>>
 */

interface Overrider<InputType, T> {
    valueBuilder: ValueBuilder<InputType, T>;
    explanationMessage?: Message<InputType>;
}

interface DefaultResolver<InputType, T> {
    valueBuilder: ValueBuilder<InputType, T>;
    noDefaultValueHelpMessage?: Message<InputType>;
}

class SingleParamResolverBuilderImpl<InputType, T>
    implements SingleParamResolverBuilder<InputType, T>
{
    private overrider: Overrider<InputType, T> | undefined = undefined;
    constructor(private readonly inputParamKey: PropertyKey<InputType>) {}

    override(
        valueBuilder: ValueBuilder<InputType, T>,
        paramMessage?: Message<InputType>
    ): SingleParamResolverBuilder<InputType, T> {
        if (this.overrider !== undefined) {
            illegalState(
                `parameter \`${String(this.inputParamKey)}\` is overriden multiple times`
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
    ): AbstractSingleParamResolver<InputType, T> {
        return new SingleParamResolverImpl(
            this.inputParamKey,
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
        noDefaultValueHelpMessage?: Message<InputType>
    ): SingleParamWithValueResolverBuilder<InputType, T> {
        return new SingleParamWithValueResolverBuilderImpl(
            this.inputParamKey,
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
            this.inputParamKey,
            this.overrider,
            undefined
        );
    }
}

class SingleParamWithValueResolverBuilderImpl<InputType, T>
    implements SingleParamWithValueResolverBuilder<InputType, T>
{
    constructor(
        private readonly inputParamKey?: PropertyKey<InputType>,
        private readonly overrider?: Overrider<InputType, T>,
        private readonly defaultResolver?: DefaultResolver<InputType, T>
    ) {}

    validate(
        ...validationRules: ValidationRule<InputType, T>[]
    ): AbstractSingleParamResolver<InputType, T> {
        return new SingleParamResolverImpl(
            this.inputParamKey,
            this.overrider,
            this.defaultResolver,
            validationRules
        );
    }

    noValidationNeeded(): AbstractSingleParamResolver<InputType, T> {
        return new SingleParamResolverImpl(
            this.inputParamKey,
            this.overrider,
            this.defaultResolver,
            []
        );
    }

    validateAtRuntimeOnly(): AbstractSingleParamResolver<InputType, T> {
        return this.noValidationNeeded();
    }
}

class SingleParamResolverImpl<InputType, T> extends AbstractSingleParamResolver<
    InputType,
    T
> {
    constructor(
        private readonly inputParamKey?: PropertyKey<InputType>,
        private readonly overrider?: Overrider<InputType, T>,
        private readonly defaultResolver?: DefaultResolver<InputType, T>,
        private readonly validationRules: ValidationRule<InputType, T>[] = [],
        private readonly overridenWithMockValue: boolean = false
    ) {
        super();
    }

    /**
     * Unfortunately, since the language does not allow to validate the type of the parameter properly,
     * no actual type checking is performed.
     */
    resolveParam(inputParams: InputType): SingleParamResolutionResult<T> {
        const result: SingleParamResolutionResult<T> = {
            inputParamName:
                this.inputParamKey === undefined
                    ? undefined
                    : String(this.inputParamKey),
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

        value = this.tryToReadInputValue(inputParams, result);

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

    protected tryToReadInputValue(
        inputParams: InputType,
        result: SingleParamResolutionResult<T>
    ): T | undefined {
        if (this.inputParamKey === undefined) {
            return undefined;
        }
        const userValue = inputParams[this.inputParamKey];
        if (userValue === undefined) {
            return undefined;
        }
        // if user specified a value, then take it
        const userValueAsT = userValue as T;
        if (userValueAsT !== null) {
            result.inputReadCorrectly = {
                wasPerformed: true,
                withValue: userValueAsT,
            };
            return userValueAsT;
        } else {
            // unfortunately, this case is unreachable: TypeScript does not provide the way to check that `userValue` is of the `T` type indeed
            // TODO: actually, it does: the type validator should be passed and used (for example, Ajv one)
            unreachable(
                "cast of `any` to generic `T` type should always succeed, ",
                `value = ${stringifyAnyValue(userValue)} for ${this.quotedName()} parameter`
            );
        }
    }

    /**
     * @returns a new `value` value and true if `result` is complete, false otherwise
     */
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
            // no checks and logs are needed, just return the mock value
            result.resultValue = valueToOverrideWith;
            if (valueToOverrideWith === undefined) {
                illegalState(
                    `${this.quotedName()} is expected to be a mock value, `,
                    "but its builder resolves with `undefined`"
                );
            }
            return [valueToOverrideWith, true];
        }
        if (value === valueToOverrideWith) {
            return [value, false];
        }
        result.overriden = {
            wasPerformed: true,
            withValue: valueToOverrideWith,
            message: buildMessage(explanationMessage, inputParams),
        };
        return [valueToOverrideWith, false];
    }

    /**
     * @returns a new `value` value and true if `result` is complete, false otherwise
     */
    private tryToResolveWithDefault(
        inputParams: InputType,
        result: SingleParamResolutionResult<T>,
        value: T | undefined
    ): [T | undefined, boolean] {
        // if user value is still undefined after overriden resolution, resolve with default
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
            const helpMessageSuffix =
                noDefaultValueHelpMessage === undefined
                    ? ""
                    : `. ${buildMessage(noDefaultValueHelpMessage, inputParams)}`;
            result.isInvalidCause = `${this.noValueMessage()}${helpMessageSuffix}`;
            return [value, true];
        }
        return [value, false];
    }

    /**
     * @returns true if `value` is valid, false otherwise
     */
    private validateDefinedValue(
        inputParams: InputType,
        result: SingleParamResolutionResult<T>,
        value: T
    ): boolean {
        for (const [validateValue, paramShouldMessage] of this
            .validationRules) {
            const validationResult = validateValue(value, inputParams);
            if (!validationResult) {
                result.isInvalidCause = `${this.quotedName()} should ${buildMessage(paramShouldMessage, inputParams)}, but has value ${stringifyDefinedValue(value)}`;
                return false;
            }
        }
        return true;
    }

    private quotedName(): string {
        return `\`${String(this.inputParamKey)}\``;
    }

    private noValueMessage(): string {
        return `${this.quotedName()} is required, but neither a user value nor a default one is specified`;
    }
}
