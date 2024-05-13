import { ParamsResolutionResult, ParamsResolver } from "./abstractResolvers";
import { SingleParamResolutionResult } from "./abstractResolvers";
import {
    SingleParamResolverBuilder,
    SingleParamWithValueResolverBuilder,
    StrictValueBuilder,
    insertParam,
    resolveParam,
} from "./builders";
import { accessParamByName } from "./paramAccessor";

// Notes:
// * every property should be of ParamsResolver<InputType, any> type
// * how to specify properties names:
// - property's name should be equal to the one of ResolveToType properties
// - `inputParamName` should be a path to one of the properties of InputType
export class ParamsResolverImpl<InputType, ResolveToType>
    implements ParamsResolver<InputType, ResolveToType>
{
    protected resolveParam<T>(
        inputParamName: string
    ): SingleParamResolverBuilder<InputType, T> {
        return resolveParam<InputType, T>(inputParamName);
    }

    protected insertParam<T>(
        valueBuilder: StrictValueBuilder<InputType, T>
    ): SingleParamWithValueResolverBuilder<InputType, T> {
        return insertParam<InputType, T>(valueBuilder);
    }

    protected resolveNestedParams<ParamInputType, T>(
        inputParamName: string,
        nestedParamsResolver: ParamsResolver<ParamInputType, T>
    ): ParamsResolver<InputType, T> {
        return {
            resolve(inputParams: InputType): ParamsResolutionResult<T> {
                const paramInputValue = (accessParamByName(
                    inputParams,
                    inputParamName
                ) ?? {}) as ParamInputType;
                const paramResolutionResult =
                    nestedParamsResolver.resolve(paramInputValue);
                return {
                    resolved: paramResolutionResult.resolved,
                    resolutionLogs: paramResolutionResult.resolutionLogs.map(
                        (paramLog) => {
                            return {
                                ...paramLog,
                                inputParamName: `${inputParamName}.${paramLog.inputParamName}`,
                            };
                        }
                    ),
                };
            },
        };
    }

    resolve(inputParams: InputType): ParamsResolutionResult<ResolveToType> {
        const resolvedParamsObject: { [key: string]: any } = {};
        const resolutionLogs: SingleParamResolutionResult<any>[] = [];
        let resolutionFailed = false;

        for (const prop in this) {
            if (!Object.prototype.hasOwnProperty.call(this, prop)) {
                continue;
            }
            const paramResolver = this[prop] as ParamsResolver<InputType, any>;
            if (paramResolver === null) {
                throw Error(
                    `\`ParamsResolver\` is configured incorrectly because of "${prop}": all properties should be built up to \`ParamsResolver<InputType, any>\` type`
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
        if (resolvedParams === null) {
            throw new Error(
                `\`ParamsResolver\` is configured incorrectly: resulting "${JSON.stringify(resolvedParamsObject)}" could not be interpreted as \`ResolveToType\` object`
            );
        }
        return {
            resolved: resolvedParams,
            resolutionLogs: resolutionLogs,
        };
    }
}
