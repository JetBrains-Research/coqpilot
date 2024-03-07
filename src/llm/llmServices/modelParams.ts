export interface MultiroundProfile {
    // cannot be overriden: proof will always be updated no more than `maxRoundsNumber` times
    maxRoundsNumber: number;

    // can be overriden in the `fixProof` call with the `choices` parameter
    fixedProofChoices: number;
}

export interface ModelParams {
    modelName: string;
    systemPromt: string;
    newMessageMaxTokens: number;
    tokensLimit: number;
    multiroundProfile: MultiroundProfile;
}

export interface OpenAiModelParams extends ModelParams {
    temperature: number;
    apiKey: string;
}

export interface GrazieModelParams extends ModelParams {
    apiKey: string;
}

export interface PredefinedProofsModelParams extends ModelParams {
    // A list of tactics to try to solve the goal with.
    tactics: string[];
}
