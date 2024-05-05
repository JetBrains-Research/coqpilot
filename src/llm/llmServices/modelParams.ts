export interface MultiroundProfile {
    maxRoundsNumber: number;
    proofFixChoices: number;
    proofFixPrompt: string;
}

export interface ModelParams {
    modelId: string;
    systemPrompt: string;
    maxTokensToGenerate: number;
    tokensLimit: number;
    multiroundProfile: MultiroundProfile;
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
