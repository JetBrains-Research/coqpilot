/**
 * Represents the identifier of `T`'s property that can be used to access
 * the value of the property. That is, in a sense, just the name of the property.
 */
export type PropertyKey<T> = keyof T;

/**
 * Core interface for an object that is capable of resolving `InputType` into `ResolveToType`.
 *
 * The `_resolverId` member serves as a discriminator for the `ParamsResolver` type.
 */
export interface ParamsResolver<InputType, ResolveToType> {
    resolve(inputParams: InputType): ParamsResolutionResult<ResolveToType>;

    /**
     * Should be set to "ParamsResolver" value in any implementation object.
     */
    _resolverId: "ParamsResolver";
}

/**
 * Contains both the resolved parameters object `resolved` and the resolution logs `resolutionLogs`.
 * If resolution does not succeed, `resolved` is undefined.
 */
export interface ParamsResolutionResult<ResolveToType> {
    resolved?: ResolveToType;
    resolutionLogs: SingleParamResolutionResult<any>[];
}

/**
 * Interface for an object capable of resolving a single parameter.
 *
 * Practically, it can be easily represented as `ParamsResolver<InputType, T>`.
 * However, since interfaces cannot have a default method implementation,
 * this logic is only available through `AbstractSingleParamResolver`, which
 * implements both interfaces.
 */
export interface SingleParamResolver<InputType, T> {
    resolveParam(inputParams: InputType): SingleParamResolutionResult<T>;
}

/**
 * Interface that stores information about the resolution of a single parameter.
 */
export interface SingleParamResolutionResult<T> {
    /**
     * Undefined if the parameter was overriden with a mock value.
     * Otherwise contains the name of the input parameter to resolve.
     */
    inputParamName?: string;

    /**
     * Contains the resulting parameter value after its resolution
     * if successful. On failure, `resultValue` is undefined.
     */
    resultValue?: T;

    /**
     * If resolution fails, contains the message explaining the cause.
     * Otherwise, it is undefined.
     */
    isInvalidCause?: string;

    /**
     * `inputReadCorrectly.wasPerformed` is true iff the parameter's input value
     * is read as a defined value (of the correct type, if it is verifiable).
     */
    inputReadCorrectly: ResolutionActionResult<T>;

    /**
     * `overriden.wasPerformed` is true iff the parameter's input value is overriden with a new value.
     * I.e. if an override attempt is made with the same value as the input,
     * `overriden.wasPerformed` will be false.
     */
    overriden: ResolutionActionDetailedResult<T>;

    /**
     * `resolvedWithDefault.wasPerformed` is true iff the default resolver is called,
     * i.e. iff the parameter's value is undefined after input read and potential override.
     * Note: even if the default resolver returned undefined, `resolvedWithDefault.wasPerformed` will be true.
     */
    resolvedWithDefault: ResolutionActionResult<T>;
}

/**
 * `withValue` is set only if `wasPerformed` is true. However, it can be set with undefined too.
 */
export interface ResolutionActionResult<T> {
    wasPerformed: boolean;
    withValue?: T;
}

/**
 * The same as `ResolutionActionResult`, but provides an explanation message
 * if the action was performed.
 */
export interface ResolutionActionDetailedResult<T>
    extends ResolutionActionResult<T> {
    message?: string;
}

/**
 * Checks whether `object` is of `ParamsResolver` type.
 * To do this, the implementation uses the `ParamsResolver._resolverId` discriminator only.
 */
export function isParamsResolver(
    object: any
): object is ParamsResolver<any, any> {
    return object._resolverId === "ParamsResolver";
}

/**
 * This abstract class extends the `SingleParamResolver` implementation
 * with a default `resolve` method implementation to implement the `ParamsResolver` interface.
 *
 * If you plan to implement `SingleParamResolver`, you most likely want to extend this class.
 */
export abstract class AbstractSingleParamResolver<InputType, T>
    implements SingleParamResolver<InputType, T>, ParamsResolver<InputType, T>
{
    abstract resolveParam(
        inputParams: InputType
    ): SingleParamResolutionResult<T>;

    resolve(inputParams: InputType): ParamsResolutionResult<T> {
        const paramResolutionResult = this.resolveParam(inputParams);
        return {
            resolved: paramResolutionResult.resultValue,
            resolutionLogs: [paramResolutionResult],
        };
    }

    _resolverId: "ParamsResolver" = "ParamsResolver";
}
