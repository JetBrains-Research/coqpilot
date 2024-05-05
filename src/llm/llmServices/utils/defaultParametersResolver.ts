import { ParametersResolutionError } from "../../llmServiceErrors";
import { UserModelParams } from "../../userModelParams";
import { ModelParams, MultiroundProfile } from "../modelParams";

import { modelName } from "./modelParamsAccessors";

export function resolveParametersWithDefaultsImpl(
    params: UserModelParams
): ModelParams {
    const modelNameOrEmpty = modelName(params) ?? "";
    const newMessageMaxTokens =
        params.newMessageMaxTokens ??
        defaultNewMessageMaxTokens[modelNameOrEmpty];
    const tokensLimit =
        params.tokensLimit ?? defaultTokensLimits[modelNameOrEmpty];
    const systemMessageContent =
        params.systemPrompt ?? defaultSystemMessageContent;
    const multiroundProfile: MultiroundProfile = {
        maxRoundsNumber:
            params.multiroundProfile?.maxRoundsNumber ??
            defaultMultiroundProfile.maxRoundsNumber,
        proofFixChoices:
            params.multiroundProfile?.proofFixChoices ??
            defaultMultiroundProfile.proofFixChoices,
        proofFixPrompt:
            params.multiroundProfile?.proofFixPrompt ??
            defaultMultiroundProfile.proofFixPrompt,
    };
    if (newMessageMaxTokens === undefined) {
        throw new ParametersResolutionError(
            "no default value for `newMessageMaxTokens`",
            params
        );
    }
    if (tokensLimit === undefined) {
        throw new ParametersResolutionError(
            "no default value for `tokensLimit`",
            params
        );
    }

    /** NOTE: it's important to pass `...params` first
     * because if so, then the omitted fields of the `params`
     * (`systemPromt`, `newMessageMaxTokens`, `tokensLimit`, etc)
     * will be overriden - and not in the opposite way!
     */
    return {
        ...params,
        systemPrompt: systemMessageContent,
        newMessageMaxTokens: newMessageMaxTokens,
        tokensLimit: tokensLimit,
        multiroundProfile: multiroundProfile,
    };
}

export const defaultNewMessageMaxTokens: {
    [modelName: string]: number;
} = {};

export const defaultTokensLimits: {
    [modelName: string]: number;
} = {
    // eslint-disable-next-line @typescript-eslint/naming-convention
    "gpt-3.5-turbo-0301": 2000,
};

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
        "Unfortunately, the last proof is not correct. Here is the compiler's feedback: '${diagnostic}'. Please, fix the proof.",
};
