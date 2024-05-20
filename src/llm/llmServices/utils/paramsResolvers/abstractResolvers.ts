export type PropertyKey<T> = keyof T;

export interface ParamsResolver<InputType, ResolveToType> {
    resolve(inputParams: InputType): ParamsResolutionResult<ResolveToType>;
    _resolverId: "ParamsResolver";
}

export interface ParamsResolutionResult<ResolveToType> {
    resolved?: ResolveToType;
    resolutionLogs: SingleParamResolutionResult<any>[];
}

export interface SingleParamResolver<InputType, T> {
    resolveParam(inputParams: InputType): SingleParamResolutionResult<T>;
}

export interface SingleParamResolutionResult<T> {
    inputParamName?: string;
    resultValue?: T;
    isInvalidCause?: string;
    inputReadCorrectly: ResolutionActionResult<T>;
    /**
     * `overriden.wasPerformed` is true iff the parameter's input value is overriden with a new value.
     * I.e. if an override attempt is made with the same value as the input,
     * `overriden.wasPerformed` will be false.
     */
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

export function isParamsResolver(
    object: any
): object is ParamsResolver<any, any> {
    return object._resolverId === "ParamsResolver";
}

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
