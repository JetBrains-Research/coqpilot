import { ConfigurationError } from "../../llmServiceErrors";
import { UserModelParams } from "../../userModelParams";
import { ModelParams, MultiroundProfile } from "../modelParams";

import {
    SingleParamResolutionResult,
    SingleParamResolver,
    SingleParamResolverBuilder,
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
    resolveParam<T>(
        inputParamName: string
    ): SingleParamResolverBuilder<InputType, T> {
        return resolveParam<InputType, T>(inputParamName);
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
            throw new ConfigurationError(
                `\`ModelParamsResolver\` is configured incorrectly: resulting "${JSON.stringify(resolvedParamsObject)}" could not be interpreted as \`ModelParams\` object`
            );
        }
        return {
            resolvedParams: resolvedParams,
            resolutionLogs: resolutionLogs,
        };
    }
}

export class BasicModelParamsResolver<
    InputType extends UserModelParams,
    ResolveToType extends ModelParams,
> extends ParamsResolver<InputType, ResolveToType> {
    modelId = this.resolveParam<string>("modelId")
        .requiredToBeConfigured()
        .noValidationNeeded();

    systemPrompt = this.resolveParam<string>("systemPrompt")
        .default((_) => defaultSystemMessageContent)
        .noValidationNeeded();

    multiroundProfile = this.resolveParam<MultiroundProfile>(
        "multiroundProfile"
    )
        .default((userModelParams) => {
            const userMultiroundProfile = userModelParams.multiroundProfile;
            return {
                maxRoundsNumber:
                    userMultiroundProfile?.maxRoundsNumber ??
                    defaultMultiroundProfile.maxRoundsNumber,
                proofFixChoices:
                    userMultiroundProfile?.proofFixChoices ??
                    defaultMultiroundProfile.proofFixChoices,
                proofFixPrompt:
                    userMultiroundProfile?.proofFixPrompt ??
                    defaultMultiroundProfile.proofFixPrompt,
            };
        })
        .validate(
            [(profile) => profile.maxRoundsNumber > 0, "be positive"],
            [(profile) => profile.proofFixChoices > 0, "be positive"]
        );
}

export const defaultSystemMessageContent: string =
    "Generate proof of the theorem from user input in Coq. You should only generate proofs in Coq. Never add special comments to the proof. Your answer should be a valid Coq proof. It should start with 'Proof.' and end with 'Qed.'.";

/**
 * Properties of `defaultMultiroundProfile` can be used separately.
 * - Multiround is disabled by default.
 * - 1 fix version per proof by default.
 * - Default `proofFixPrompt` includes `${diagnostic}` message.
 */
export const defaultMultiroundProfile: MultiroundProfile = {
    maxRoundsNumber: 1,
    proofFixChoices: 1,
    proofFixPrompt:
        "Unfortunately, the last proof is not correct. Here is the compiler's feedback: `${diagnostic}`. Please, fix the proof.",
};
