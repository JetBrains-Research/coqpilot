export interface MultiroundProfile {
    maxRoundsNumber: number;
    /**
     * Is handled the same way as `ModelParams.defaultChoices` is, i.e. `defaultProofFixChoices` is used
     * only as a default `choices` value in the corresponding `fixProof` facade method.
     *
     * Do not use it inside the implementation, use the `choices` instead.
     */
    defaultProofFixChoices: number;
    proofFixPrompt: string;
}

export interface ModelParams {
    modelId: string;
    systemPrompt: string;
    maxTokensToGenerate: number;
    tokensLimit: number;
    multiroundProfile: MultiroundProfile;

    /**
     * Always overriden by the `choices` parameter at the call site, if one is specified.
     * I.e. `defaultChoices` is used only as a default `choices` value in the corresponding facade methods.
     *
     * Do not use it inside the implementation, use the `choices` instead.
     */
    defaultChoices: number;
}

export interface PredefinedProofsModelParams extends ModelParams {
    tactics: string[];
}

export interface OpenAiModelParams extends ModelParams {
    modelName: string;
    temperature: number;
    apiKey: string;
}

export interface GrazieModelParams extends ModelParams {
    modelName: string;
    apiKey: string;
}

export interface LMStudioModelParams extends ModelParams {
    temperature: number;
    port: number;
}
