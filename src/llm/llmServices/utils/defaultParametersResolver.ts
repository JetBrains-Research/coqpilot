import { UserModelParams } from "../../userModelParams";
import { ModelParams, MultiroundProfile } from "../modelParams";

export function resolveParametersWithDefaultsImpl(
    params: UserModelParams
): ModelParams {
    const newMessageMaxTokens =
        params.newMessageMaxTokens ??
        defaultNewMessageMaxTokens[params.modelName];
    const tokensLimits =
        params.tokensLimit ?? defaultTokensLimits[params.modelName];
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
    if (newMessageMaxTokens === undefined || tokensLimits === undefined) {
        throw Error(`user model parameters cannot be resolved: ${params}`);
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
        tokensLimit: tokensLimits,
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

// its properties can be used separately
export const defaultMultiroundProfile: MultiroundProfile = {
    maxRoundsNumber: 1, // multiround is disabled by default
    proofFixChoices: 1, // 1 fix version per proof by default
    proofFixPrompt:
        "Unfortunately, the last proof is not correct. Here is the compiler's feedback: '${diagnostic}'. Please, fix the proof.",
};
