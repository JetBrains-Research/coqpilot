import { Theorem } from "../../coqParser/parsedTypes";
import { JSONSchemaType } from "ajv";

export interface ProofGenerationContext {
    sameFileTheorems: Theorem[];
    admitCompletionTarget: string;
}

export interface ModelParams {}

export interface OpenAiModelParams extends ModelParams {
    prompt: string;
    // The maximum number of tokens that can be generated in the chat completion.
    answerMaxTokens: number;
    // Input length + generated tokens max length.
    modelContextLength: number;
    temperature: number;
    model: string;
    apiKey: string;
    choices: number;
}

export interface GrazieModelParams extends ModelParams {
    prompt: string;
    // Input length + generated tokens max length.
    modelContextLength: number;
    model: string;
    apiKey: string;
    choices: number;
}

export interface PredefinedProofsModelParams extends ModelParams {
    // A list of tactics to try to solve the goal with.
    tactics: string[];
}

export const openAiModelParamsSchema: JSONSchemaType<OpenAiModelParams> = {
    type: "object",
    properties: {
        prompt: { type: "string" },
        answerMaxTokens: { type: "number" },
        modelContextLength: { type: "number" },
        temperature: { type: "number" },
        model: { type: "string" },
        apiKey: { type: "string" },
        choices: { type: "number" },
    },
    required: [
        "prompt",
        "answerMaxTokens",
        "modelContextLength",
        "temperature",
        "model",
        "apiKey",
        "choices",
    ],
};

export const grazieModelParamsSchema: JSONSchemaType<GrazieModelParams> = {
    type: "object",
    properties: {
        prompt: { type: "string" },
        modelContextLength: { type: "number" },
        model: { type: "string" },
        apiKey: { type: "string" },
        choices: { type: "number" },
    },
    required: ["prompt", "modelContextLength", "model", "apiKey", "choices"],
};

export const predefinedProofsModelParamsSchema: JSONSchemaType<PredefinedProofsModelParams> =
    {
        type: "object",
        properties: {
            tactics: {
                type: "array",
                items: { type: "string" },
            },
        },
        required: ["tactics"],
    };
