export interface ParamsResolver<InputType, ResolveToType> {
    resolve(inputParams: InputType): ParamsResolutionResult<ResolveToType>;
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

export abstract class AbstractSingleParamResolverImpl<InputType, T>
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
}
