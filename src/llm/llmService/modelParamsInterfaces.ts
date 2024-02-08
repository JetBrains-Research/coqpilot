import { Theorem } from "../../lib/pvTypes";

export interface CompletionContext {
    sameFileTheorems: Theorem[];
    admitCompletionTarget: string; 
}

export interface ModelParams {}

export interface OpenAiModelParams extends ModelParams {
    prompt: string;
    maxTokens: number;
    temperature: number;
    model: string;
    apiKey: string;
    choices: number;
}

export interface GrazieModelParams extends ModelParams {
    prompt: string;
    model: string;
    apiKey: string;
    choices: number;
}

export interface PredefinedCompletionModelParams extends ModelParams {
    // A list of tactics to try to solve the goal with.
    tactics: string[];
}