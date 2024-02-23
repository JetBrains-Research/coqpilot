import { Theorem } from "../../coqParser/parsedTypes";
import { JSONSchemaType } from "ajv";

export interface ProofGenerationContext {
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

export interface PredefinedProofsModelParams extends ModelParams {
    // A list of tactics to try to solve the goal with.
    tactics: string[];
}

export const openAiModelParamsSchema: JSONSchemaType<OpenAiModelParams> = {
    $schema: "https://json-schema.org/draft/2019-09/schema",
    type: "object",
    required: [
        "prompt",
        "maxTokens",
        "temperature",
        "model",
        "apiKey",
        "choices",
    ],
    properties: {
        prompt: { type: "string" },
        maxTokens: { type: "number" },
        temperature: { type: "number" },
        model: { type: "string" },
        apiKey: { type: "string" },
        choices: { type: "number" },
    },
};

export const grazieModelParamsSchema: JSONSchemaType<GrazieModelParams> = {
    $schema: "https://json-schema.org/draft/2019-09/schema",
    required: ["prompt", "model", "apiKey", "choices"],
    type: "object",
    properties: {
        prompt: { type: "string" },
        model: { type: "string" },
        apiKey: { type: "string" },
        choices: { type: "number" },
    },
};

export const predefinedProofsModelParamsSchema: JSONSchemaType<PredefinedProofsModelParams> =
    {
        $schema: "https://json-schema.org/draft/2019-09/schema",
        type: "object",
        required: ["tactics"],
        properties: {
            tactics: {
                type: "array",
                items: {
                    type: "string",
                },
            },
        },
    };
