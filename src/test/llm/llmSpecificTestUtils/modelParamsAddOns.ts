import { MultiroundProfile } from "../../../llm/llmServices/modelParams";
import { UserMultiroundProfile } from "../../../llm/userModelParams";

export interface UserModelParamsAddOns {
    modelId?: string;
    choices?: number;
    systemPrompt?: string;
    maxTokensToGenerate?: number;
    tokensLimit?: number;
    multiroundProfile?: UserMultiroundProfile;
}

export interface PredefinedProofsUserModelParamsAddOns
    extends UserModelParamsAddOns {
    tactics?: string[];
}

export interface OpenAiUserModelParamsAddOns extends UserModelParamsAddOns {
    modelName?: string;
    temperature?: number;
    apiKey?: string;
}

export interface GrazieUserModelParamsAddOns extends UserModelParamsAddOns {
    modelName?: string;
    apiKey?: string;
}

export interface LMStudioUserModelParamsAddOns extends UserModelParamsAddOns {
    temperature?: number;
    port?: number;
}

export interface ModelParamsAddOns {
    modelId?: string;
    choices?: number;
    systemPrompt?: string;
    maxTokensToGenerate?: number;
    tokensLimit?: number;
    multiroundProfile?: MultiroundProfile;
}

export interface MultiroundProfileAddOns {
    maxRoundsNumber?: number;
    defaultProofFixChoices?: number;
    proofFixPrompt?: string;
}
