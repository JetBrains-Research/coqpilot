import { JSONSchemaType, ValidateFunction } from "ajv";

import {
    AjvMode,
    buildAjv,
    failedAjvValidatorErrorsAsString,
} from "../../../../utils/ajvErrorsHandling";
import { throwError } from "../../../../utils/throwErrors";

import {
    ParamsResolutionResult,
    ParamsResolver,
    isParamsResolver,
} from "./abstractResolvers";
import { SingleParamResolutionResult } from "./abstractResolvers";
import { PropertyKey } from "./abstractResolvers";
import {
    SingleParamResolverBuilder,
    SingleParamWithValueResolverBuilder,
    StrictValueBuilder,
    newParam,
    resolveParam,
} from "./builders";

/**
 * Generic type check that returns `any` if `T` has no optional properties,
 * i.e. properties that could be set with `undefined` value.
 * Otherwise, returns `never`.
 *
 * This check is supposed to be used as follows: `T extends NoOptionalProperties<T>`.
 * However, it is already used to restrict `ResolveToType` of `ParamsResolverImpl`,
 * so most likely you don't need to use it by yourself.
 */
export type NoOptionalProperties<T> = [
    {
        [K in keyof T]-?: undefined extends T[K] ? any : never;
    }[keyof T],
] extends [never]
    ? any
    : never;

/**
 * Implement this type every time you develop a new `ParamsResolverImpl`.
 * It checks that you have specified the correct resolvers for all `ResolveToType` properties.
 *
 * Unfortunately, it can only be used for statically known types, so the base `ParamsResolverImpl` class cannot extend it.
 */
export type ValidParamsResolverImpl<InputType, ResolveToType> = {
    [K in keyof ResolveToType]: ParamsResolver<InputType, ResolveToType[K]>;
};

/**
 * The base class that implements the parameters resolving algorithm and provides
 * a convenient way to declare your custom parameters resolvers.
 *
 * How to use it.
 * 1. Declare a custom class that extends `ParamsResolverImpl` with the right generic types:
 *    the `InputType` is the type of the input object to resolve and
 *    the `ResolveToType` is the type of the output resolved object.
 *
 * 2. Specify each property resolver in the following format:
 *    ```
 *    readonly resolveToParamKey = this.resolveParam<PropertyType>(inputParamKey)
 *        . // continue building the single parameter resolver with the hints
 *    ```
 *    Notes:
 *    * `resolveToParamKey` should be a name of one of the `ResolveToType` properties (and should not start with "_");
 *    * `inputParamKey` should be a name of one of the `InputType` properties;
 *    * you can also use `this.insertParam<T>(...)` and `resolveNestedParams<ParamInputType, T>(...)`
 *    instead of `this.resolveParam<PropertyType>` to start building the parameter resolver. Check their docs for more details.
 *
 *    Once you finish building the parameter resolver, it should implement `ParamsResolver<InputType, any>`
 *    (i.e. should be a finished parameter resolver) &mdash; most likely, it will be of
 *    the `AbstractSingleParamResolver<InputType, PropertyType>` class.
 *
 *    Implementation note:
 *    * if you need to declare any utility properties in your class,
 *      it is okay to do by starting the property name with an underscore (for example, `_utilityProp`).
 *
 * 3. Check that all resolvers for the `ResolveToType` properties are specified correctly. To do this, make your
 *    parameters resolver class implement `ValidParamsResolverImpl<InputType, ResolveToType>`. It will check exactly this contract.
 *
 * 4. Specify an Ajv JSON schema for `ResolveToType` and pass it to the `super(...)` constructor. So far it is needed to
 *    properly validate the properties inside the resulting resolved object. *TODO: make `ParamsResolverImpl` generate such a schema.*
 *
 * 5. Call `resolve(inputParams: InputType): ParamsResolutionResult<ResolveToType>` method of your custom class
 *    to validate the `inputParams` parameters robustly and efficiently. The parameters resolver has no visible inner state,
 *    so can be called multiple times with no side-effects.
 */
export abstract class ParamsResolverImpl<
    InputType,
    ResolveToType extends NoOptionalProperties<ResolveToType>,
> implements ParamsResolver<InputType, ResolveToType>
{
    private readonly _resolveToTypeValidator: ValidateFunction<ResolveToType>;
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

    /**
     * Creates a builder of the resolver that resolves `InputType[inputParamKey]`.
     */
    protected resolveParam<T>(
        inputParamKey: PropertyKey<InputType>
    ): SingleParamResolverBuilder<InputType, T> {
        return resolveParam<InputType, T>(inputParamKey);
    }

    /**
     * Creates a builder of the resolver that resolves a new property.
     * In other words, this is the way to build the property of the `ResolveToType` object
     * that does not have a corresponding property inside `InputType`.
     */
    protected insertParam<T>(
        valueBuilder: StrictValueBuilder<InputType, T>
    ): SingleParamWithValueResolverBuilder<InputType, T> {
        return newParam<InputType, T>(valueBuilder);
    }

    /**
     * Similarly to the `resolveParam` method, creates a resolver that resolves `InputType[inputParamKey]`.
     * However, `inputParamKey` will be resolved via the standalone `nestedParamsResolver` resolver.
     * Practically, this is the proper way to resolve the properties of the nested object separately,
     * instead of resolving them all together as a single parameter having the nested object value.
     *
     * Moreover, since this method returns a finished resolver instead of a builder,
     * so far there is no way to declare a whole-nested-object resolution rules (overrides and defaults)
     * at the same time with using a standalone parameters resolver for the nested parameters.
     * Thus, you need to choose whether to resolve the nested object as a single object or parameter-by-parameter.
     *
     * Notes on the nested parameters resolution algorithm.
     * - If `InputType[inputParamKey]` turns out to be undefined, an empty object `{}` will be passed to
     *   the `nestedParamsResolver.resolve` method as the input.
     * - All names of the parameters of the nested `ParamInputType` will be prepended with `${inputParamKey}.`
     *   in the resolution logs.
     * - The resolution logs of the nested `ParamInputType` properties will be merged with the resolution logs
     *   of the other `InputType` properties and returned in the `resolve` method.
     */
    protected resolveNestedParams<ParamInputType, T>(
        inputParamKey: PropertyKey<InputType>,
        nestedParamsResolver: ParamsResolver<ParamInputType, T>
    ): ParamsResolver<InputType, T> {
        return new (class {
            resolve(inputParams: InputType): ParamsResolutionResult<T> {
                const paramInputValue = (inputParams[inputParamKey] ??
                    {}) as ParamInputType;
                const paramResolutionResult =
                    nestedParamsResolver.resolve(paramInputValue);
                return {
                    resolved: paramResolutionResult.resolved,
                    resolutionLogs: paramResolutionResult.resolutionLogs.map(
                        (paramLog) => {
                            return {
                                ...paramLog,
                                inputParamName: `${String(inputParamKey)}.${paramLog.inputParamName}`,
                            };
                        }
                    ),
                };
            }
            _resolverId: "ParamsResolver" = "ParamsResolver";
        })();
    }

    /**
     * Core method of the parameters resolver that actually resolves the input parameters object `inputParams`
     * into the resolved parameters object of the `ResolveToType` type.
     *
     * However, `resolve` does not return the resolved parameters object directly, instead,
     * it returns the `ParamsResolutionResult<ResolveToType>` object containing both resolved object `resolved`
     * (in case of a failure it is undefined) and the resolution logs `resolutionLogs`.
     * You can find more details in the `ParamsResolutionResult`'s docs.
     *
     * This method `resolve` can be called multiple times, there is no inner state preventing from that.
     *
     * Finally, the `resolve` method throws errors only if it is not configured correctly
     * (has properties of the wrong format or the single-parameter resolvers provided cannot produce a valid `ResolveToType` object `(*)`).
     * If the reason of the resolution failure are `inputParams` parameters, the cause will be descibed in the resulting logs being returned
     * and no error will be thrown.
     *
     * Note on `(*)`: unfortunately, an error can happen in one more case, namely, if the `inputParams` object
     * has properties of wrong types (masked with `any`). In this case, the specified validation checks for these parameters
     * might throw, or, if the checks luckily pass, the schema of `ResolveToType` will cause an error thrown in the end.
     * Thus, be careful with using unsafe type casts or consider verifying `inputParams` with its Ajv JSON schema first.
     */
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
            // no generic parametrization check in runtime is possible, unfortunately
            if (!isParamsResolver(paramResolver)) {
                throwError(
                    `\`ParamsResolver\` is configured incorrectly because of \`${prop}\`: `,
                    "all properties should be built up to `ParamsResolver<InputType, any>` type"
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
            throwError(
                "`ParamsResolver` is most likely configured incorrectly. ",
                `Resulting object could not be interpreted as \`${this._resolveToTypeName}\`: `,
                `${failedAjvValidatorErrorsAsString(this._resolveToTypeValidator)}.`
            );
        }
        return {
            resolved: resolvedParams,
            resolutionLogs: resolutionLogs,
        };
    }

    _resolverId: "ParamsResolver" = "ParamsResolver";
}
