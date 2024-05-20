import { DefinedError, JSONSchemaType, ValidateFunction } from "ajv";

import {
    AjvMode,
    ajvErrorsAsString,
    buildAjv,
} from "../../../../utils/ajvErrorsHandling";

import {
    ParamsResolutionResult,
    ParamsResolver,
    isParamsResolver,
} from "./abstractResolvers";
import { SingleParamResolutionResult } from "./abstractResolvers";
import {
    SingleParamResolverBuilder,
    SingleParamWithValueResolverBuilder,
    StrictValueBuilder,
    newParam,
    resolveParam,
} from "./builders";
import { accessParamByName } from "./paramAccessor";

export type NoOptionalProperties<T> = [
    {
        [K in keyof T]-?: undefined extends T[K] ? any : never;
    }[keyof T],
] extends [never]
    ? any
    : never;

export type PropertyName<T> = keyof T;

/**
 * Implement this type every time you develop a new `ParamsResolverImpl`.
 * It checks that you have specified the correct resolvers for all `ResolveToType` properties.
 *
 * Unfortunately, it can only be used for statically known types, so the base `ParamsResolverImpl` cannot extend it.
 */
export type ValidParamsResolverImpl<InputType, ResolveToType> = {
    [K in keyof ResolveToType]: ParamsResolver<InputType, ResolveToType[K]>;
};

// Notes:
// * every property should be of ParamsResolver<InputType, any> type
// * how to specify properties names:
// - property's name should be equal to the one of ResolveToType properties (and should not start with "_")
// - `inputParamName` should be a path to one of the properties of InputType
export abstract class ParamsResolverImpl<
    InputType,
    ResolveToType extends NoOptionalProperties<ResolveToType>,
> implements ParamsResolver<InputType, ResolveToType>
{
    protected readonly _resolveToTypeValidator: ValidateFunction<ResolveToType>;
    protected readonly _resolveToTypeName: string;

    constructor(
        resolvedParamsSchema: JSONSchemaType<ResolveToType>,
        resolveToTypeName: string
    ) {
        this._resolveToTypeName = resolveToTypeName;
        this._resolveToTypeValidator = buildAjv(
            AjvMode.COLLECT_ALL_ERRORS
        ).compile(resolvedParamsSchema) as ValidateFunction<ResolveToType>;
    }

    protected resolveParam<T>(
        inputParamName: PropertyName<InputType>
    ): SingleParamResolverBuilder<InputType, T> {
        return resolveParam<InputType, T>(inputParamName as string);
    }

    protected insertParam<T>(
        valueBuilder: StrictValueBuilder<InputType, T>
    ): SingleParamWithValueResolverBuilder<InputType, T> {
        return newParam<InputType, T>(valueBuilder);
    }

    // TODO: enhance this method and builders to make resolution-with-default possible for nested objects
    // (for example: all props of nested object are required, but in top-level object this nested param is in general optional)
    protected resolveNestedParams<ParamInputType, T>(
        inputParamName: PropertyName<InputType>,
        nestedParamsResolver: ParamsResolver<ParamInputType, T>
    ): ParamsResolver<InputType, T> {
        return new (class {
            resolve(inputParams: InputType): ParamsResolutionResult<T> {
                const paramInputValue = (accessParamByName(
                    inputParams,
                    inputParamName as string
                ) ?? {}) as ParamInputType;
                const paramResolutionResult =
                    nestedParamsResolver.resolve(paramInputValue);
                return {
                    resolved: paramResolutionResult.resolved,
                    resolutionLogs: paramResolutionResult.resolutionLogs.map(
                        (paramLog) => {
                            return {
                                ...paramLog,
                                inputParamName: `${inputParamName as string}.${paramLog.inputParamName}`,
                            };
                        }
                    ),
                };
            }
            _resolverId: "ParamsResolver" = "ParamsResolver";
        })();
    }

    resolve(inputParams: InputType): ParamsResolutionResult<ResolveToType> {
        const resolvedParamsObject: { [key: string]: any } = {};
        const resolutionLogs: SingleParamResolutionResult<any>[] = [];
        let resolutionFailed = false;

        for (const prop in this) {
            if (
                !Object.prototype.hasOwnProperty.call(this, prop) ||
                prop.startsWith("_")
            ) {
                continue;
            }
            const paramResolver = this[prop] as ParamsResolver<InputType, any>;
            // no generic parametrization check is possible, unfortunately
            if (!isParamsResolver(paramResolver)) {
                throw Error(
                    `\`ParamsResolver\` is configured incorrectly because of \`${prop}\`: all properties should be built up to \`ParamsResolver<InputType, any>\` type`
                );
            }
            const paramResolutionResult = paramResolver.resolve(inputParams);
            resolutionLogs.push(...paramResolutionResult.resolutionLogs);
            if (paramResolutionResult.resolved === undefined) {
                resolutionFailed = true;
            } else {
                resolvedParamsObject[prop] = paramResolutionResult.resolved;
            }
        }

        if (resolutionFailed) {
            return {
                resolutionLogs: resolutionLogs,
            };
        }

        const resolvedParams = resolvedParamsObject as ResolveToType;
        if (!this._resolveToTypeValidator(resolvedParams)) {
            throw Error(
                `\`ParamsResolver\` is configured incorrectly. Resulting object could not be interpreted as \`${this._resolveToTypeName}\`: ${ajvErrorsAsString(this._resolveToTypeValidator.errors as DefinedError[])}.`
            );
        }
        return {
            resolved: resolvedParams,
            resolutionLogs: resolutionLogs,
        };
    }

    _resolverId: "ParamsResolver" = "ParamsResolver";
}
