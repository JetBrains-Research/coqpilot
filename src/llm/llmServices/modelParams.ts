export interface MultiroundProfile {
    maxRoundsNumber: number;
    proofFixChoices: number;
    proofFixPrompt: string;
}

export interface ModelParams {
    modelId: string;
    systemPrompt: string;
    newMessageMaxTokens: number;
    tokensLimit: number;
    multiroundProfile: MultiroundProfile;
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

export interface PredefinedProofsModelParams extends ModelParams {
    // A list of tactics to try to solve the goal with.
    tactics: string[];
}

export interface LMStudioModelParams extends ModelParams {
    temperature: number;
    port: number;
}
