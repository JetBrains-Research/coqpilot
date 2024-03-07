export interface MultiroundProfile {
    maxRoundsNumber: number;
    proofFixChoices: number;
    proofFixPromt: string;
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
