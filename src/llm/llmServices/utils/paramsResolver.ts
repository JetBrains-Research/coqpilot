import { ConfigurationError } from "../../llmServiceErrors";

import {
    SingleParamResolutionResult,
    SingleParamResolver,
    SingleParamResolverBuilder,
    SingleParamWithValueResolverBuilder,
    ValueBuilder,
    insertParam,
    resolveParam,
} from "./singleParamResolver";

export interface ParamsResolutionResult<ResolveToType> {
    resolvedParams?: ResolveToType;
    resolutionLogs: SingleParamResolutionResult<any>[];
}

// Notes:
// * every property should be of ParamWithValidatedValueResolver<*> type
// * how to specify properties names:
// - property's name should be equal to the one of ResolveToType properties
// - parameter's name in the ParamResolver should be a path to one of the properties of InputType
export class ParamsResolver<InputType, ResolveToType> {
    protected resolveParam<T>(
        inputParamName: string
    ): SingleParamResolverBuilder<InputType, T> {
        return resolveParam<InputType, T>(inputParamName);
    }

    protected insertParam<T>(
        valueBuilder: ValueBuilder<InputType, T>
    ): SingleParamWithValueResolverBuilder<InputType, T> {
        return insertParam<InputType, T>(valueBuilder);
    }

    resolve(inputParams: InputType): ParamsResolutionResult<ResolveToType> {
        const resolvedParamsObject: { [key: string]: any } = {};
        const resolutionLogs: SingleParamResolutionResult<any>[] = [];
        let resolutionFailed = false;

        for (const prop in this) {
            if (Object.prototype.hasOwnProperty.call(this, prop)) {
                const paramResolver = this[prop] as SingleParamResolver<
                    InputType,
                    any
                >;
                if (paramResolver === null) {
                    throw Error(
                        `\`ModelParamsResolver\` is configured incorrectly because of "${prop}": all properties should be built up to \`ParamWithValidatedValueResolver\` type`
                    );
                }

                const resolutionResult = paramResolver.resolve(inputParams);
                resolutionLogs.push(resolutionResult);
                if (resolutionResult.resultValue === undefined) {
                    resolutionFailed = true;
                } else {
                    resolvedParamsObject[prop] = resolutionResult.resultValue;
                }
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
                `\`ModelParamsResolver\` is configured incorrectly: resulting "${JSON.stringify(resolvedParamsObject)}" could not be interpreted as \`ModelParams\` object`
            );
        }
        return {
            resolvedParams: resolvedParams,
            resolutionLogs: resolutionLogs,
        };
    }

    resolveOrThrow(inputParams: InputType): ResolveToType {
        const resolutionResult = this.resolve(inputParams);
        if (resolutionResult.resolvedParams !== undefined) {
            return resolutionResult.resolvedParams;
        }
        const joinedErrorLogs = resolutionResult.resolutionLogs
            .filter((paramLog) => paramLog.isInvalidCause !== undefined)
            .map(
                (paramLog) =>
                    `\`${paramLog.inputParamName}\`: ${paramLog.isInvalidCause}`
            )
            .join("; ");
        throw new ConfigurationError(
            `parameters "${JSON.stringify(inputParams)}" could not be resolved: ${joinedErrorLogs}`
        );
    }
}
