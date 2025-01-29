import { JSONSchemaType } from "ajv";
import { PropertiesSchema } from "ajv/dist/types/json-schema";

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
    maxPreviousProofVersionsNumber: number;
}

export interface ModelParams {
    modelId: string;
    systemPrompt: string;

    maxTokensToGenerate: number;
    tokensLimit: number;
    maxContextTheoremsNumber: number;

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
    authType: "stgn" | "prod";
}

export interface LMStudioModelParams extends ModelParams {
    temperature: number;
    port: number;
}

export interface DeepSeekModelParams extends ModelParams {
    modelName: string;
    temperature: number;
    apiKey: string;
}

export interface ModelsParams {
    predefinedProofsModelParams: PredefinedProofsModelParams[];
    openAiParams: OpenAiModelParams[];
    grazieParams: GrazieModelParams[];
    lmStudioParams: LMStudioModelParams[];
    deepSeekParams: DeepSeekModelParams[];
}

export const multiroundProfileSchema: JSONSchemaType<MultiroundProfile> = {
    type: "object",
    properties: {
        maxRoundsNumber: { type: "number" },
        defaultProofFixChoices: { type: "number" },
        proofFixPrompt: { type: "string" },
        maxPreviousProofVersionsNumber: { type: "number" },
    },
    required: ["maxRoundsNumber", "defaultProofFixChoices", "proofFixPrompt"],
    additionalProperties: false,
};

export const modelParamsSchema: JSONSchemaType<ModelParams> = {
    type: "object",
    properties: {
        modelId: { type: "string" },

        systemPrompt: { type: "string" },

        maxTokensToGenerate: { type: "number" },
        tokensLimit: { type: "number" },
        maxContextTheoremsNumber: { type: "number" },

        multiroundProfile: {
            type: "object",
            oneOf: [multiroundProfileSchema],
        },

        defaultChoices: { type: "number" },
    },
    required: [
        "modelId",
        "systemPrompt",
        "maxTokensToGenerate",
        "tokensLimit",
        "maxContextTheoremsNumber",
        "multiroundProfile",
        "defaultChoices",
    ],
    additionalProperties: false,
};

export const predefinedProofsModelParamsSchema: JSONSchemaType<PredefinedProofsModelParams> =
    {
        title: "predefinedProofsModelsParameters",
        type: "object",
        properties: {
            tactics: {
                type: "array",
                items: { type: "string" },
            },
            ...(modelParamsSchema.properties as PropertiesSchema<ModelParams>),
        },
        required: ["tactics", ...modelParamsSchema.required],
        additionalProperties: false,
    };

export const openAiModelParamsSchema: JSONSchemaType<OpenAiModelParams> = {
    title: "openAiModelsParameters",
    type: "object",
    properties: {
        modelName: { type: "string" },
        temperature: { type: "number" },
        apiKey: { type: "string" },
        ...(modelParamsSchema.properties as PropertiesSchema<ModelParams>),
    },
    required: [
        "modelName",
        "temperature",
        "apiKey",
        ...modelParamsSchema.required,
    ],
    additionalProperties: false,
};

export const grazieModelParamsSchema: JSONSchemaType<GrazieModelParams> = {
    title: "grazieModelsParameters",
    type: "object",
    properties: {
        modelName: { type: "string" },
        apiKey: { type: "string" },
        authType: {
            type: "string",
            enum: ["stgn", "prod"],
        },
        ...(modelParamsSchema.properties as PropertiesSchema<ModelParams>),
    },
    required: [
        "modelName",
        "apiKey",
        "authType",
        ...modelParamsSchema.required,
    ],
    additionalProperties: false,
};

export const lmStudioModelParamsSchema: JSONSchemaType<LMStudioModelParams> = {
    title: "lmStudioModelsParameters",
    type: "object",
    properties: {
        temperature: { type: "number" },
        port: { type: "number" },
        ...(modelParamsSchema.properties as PropertiesSchema<ModelParams>),
    },
    required: ["temperature", "port", ...modelParamsSchema.required],
    additionalProperties: false,
};

export const deepSeekModelParamsSchema: JSONSchemaType<DeepSeekModelParams> = {
    title: "deepSeekModelsParameters",
    type: "object",
    properties: {
        modelName: { type: "string" },
        temperature: { type: "number" },
        apiKey: { type: "string" },
        ...(modelParamsSchema.properties as PropertiesSchema<ModelParams>),
    },
    required: [
        "modelName",
        "temperature",
        "apiKey",
        ...modelParamsSchema.required,
    ],
    additionalProperties: false,
};
