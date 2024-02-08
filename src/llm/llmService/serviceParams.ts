import { History } from "../types";

export interface OpenAiModelParams {
    prompt: string;
    maxTokens: number;
    temperature: number;
    model: string;
    apiKey: string;
}

export interface OpenAiServiceParams {
    choices: number;
}

export interface OpenAiRequestParams {
    serviceParams: OpenAiServiceParams;
    modelParams: OpenAiModelParams;
    history: History;
}

export interface SingleTacticModelParams {
    // A list of tactics to try to solve the goal with.
    tactics: string[];
}

export interface GrazieModelParams {
    prompt: string;
    model: string;
    apiKey: string;
}

export interface GrazieServiceParams {
    choices: number;
}

export interface GrazieRequestParams {
    serviceParams: GrazieServiceParams;
    modelParams: GrazieModelParams;
    history: History;
}