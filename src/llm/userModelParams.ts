import { JSONSchemaType } from "ajv";
import { PropertiesSchema } from "ajv/dist/types/json-schema";

export interface UserMultiroundProfile {
    /**
     * Cannot be overriden in calls, i.e.
     * proof will always be regenerated no more than `maxRoundsNumber` times.
     */
    maxRoundsNumber?: number;

    /**
     * Can be overriden in the `fixProof` call with the `choices` parameter.
     */
    proofFixChoices?: number;

    /**
     * Use `${diagnostic}` syntax to include a diagnostic message into the prompt.
     */
    proofFixPrompt?: string;

    /**
     * Specifies the maximum number of the latest proof versions
     * to include in the proof-fix chat as previous attempts to fix the proof.
     */
    maxPreviousProofVersionsNumber?: number;
}

export interface UserModelParams {
    /**
     * Can be any string, but must be unique for each specified model.
     * It is used only to distinguish models from each other.
     */
    modelId: string;

    /**
     * Can be overriden in the generation-method call with the `choices` parameter.
     */
    choices?: number;

    systemPrompt?: string;

    maxTokensToGenerate?: number;
    /**
     * Includes tokens that the model generates as an answer message,
     * i.e. should be greater than or equal to `maxTokensToGenerate`.
     */
    tokensLimit?: number;
    maxContextTheoremsNumber?: number;

    multiroundProfile?: UserMultiroundProfile;
}

export interface PredefinedProofsUserModelParams extends UserModelParams {
    /**
     * List of tactics to try to solve the goal with.
     */
    tactics: string[];
}

export interface OpenAiUserModelParams extends UserModelParams {
    modelName: string;
    temperature: number;
    apiKey: string;
}

export interface GrazieUserModelParams extends UserModelParams {
    modelName: string;
    apiKey: string;

    /**
     * Use `"stgn"` if you are an internal JetBrains AI user and `"prod"` otherwise.
     */
    authType: string;
}

export interface LMStudioUserModelParams extends UserModelParams {
    temperature: number;
    port: number;
}

export interface DeepSeekUserModelParams extends UserModelParams {
    modelName: string;
    temperature: number;
    apiKey: string;
}

export const userMultiroundProfileSchema: JSONSchemaType<UserMultiroundProfile> =
    {
        type: "object",
        properties: {
            maxRoundsNumber: { type: "number", nullable: true },
            proofFixChoices: { type: "number", nullable: true },
            proofFixPrompt: { type: "string", nullable: true },
            maxPreviousProofVersionsNumber: { type: "number", nullable: true },
        },
        required: [],
        additionalProperties: false,
    };

export const userModelParamsSchema: JSONSchemaType<UserModelParams> = {
    type: "object",
    properties: {
        modelId: { type: "string" },
        choices: { type: "number", nullable: true },

        systemPrompt: { type: "string", nullable: true },

        maxTokensToGenerate: { type: "number", nullable: true },
        tokensLimit: { type: "number", nullable: true },
        maxContextTheoremsNumber: { type: "number", nullable: true },

        multiroundProfile: {
            type: "object",
            oneOf: [userMultiroundProfileSchema],
            nullable: true,
        },
    },
    required: ["modelId"],
    additionalProperties: false,
};

export const predefinedProofsUserModelParamsSchema: JSONSchemaType<PredefinedProofsUserModelParams> =
    {
        title: "predefinedProofsModelsParameters",
        type: "object",
        properties: {
            tactics: {
                type: "array",
                items: { type: "string" },
            },
            ...(userModelParamsSchema.properties as PropertiesSchema<UserModelParams>),
        },
        required: ["modelId", "tactics"],
        additionalProperties: false,
    };

export const openAiUserModelParamsSchema: JSONSchemaType<OpenAiUserModelParams> =
    {
        title: "openAiModelsParameters",
        type: "object",
        properties: {
            modelName: { type: "string" },
            temperature: { type: "number" },
            apiKey: { type: "string" },
            ...(userModelParamsSchema.properties as PropertiesSchema<UserModelParams>),
        },
        required: ["modelId", "modelName", "temperature", "apiKey"],
        additionalProperties: false,
    };

export const grazieUserModelParamsSchema: JSONSchemaType<GrazieUserModelParams> =
    {
        title: "grazieModelsParameters",
        type: "object",
        properties: {
            modelName: { type: "string" },
            apiKey: { type: "string" },
            authType: { type: "string" },
            ...(userModelParamsSchema.properties as PropertiesSchema<UserModelParams>),
        },
        required: ["modelId", "modelName", "apiKey", "authType"],
        additionalProperties: false,
    };

export const lmStudioUserModelParamsSchema: JSONSchemaType<LMStudioUserModelParams> =
    {
        title: "lmStudioModelsParameters",
        type: "object",
        properties: {
            temperature: { type: "number" },
            port: { type: "number" },
            ...(userModelParamsSchema.properties as PropertiesSchema<UserModelParams>),
        },
        required: ["modelId", "temperature", "port"],
        additionalProperties: false,
    };

export const deepSeekUserModelParamsSchema: JSONSchemaType<DeepSeekUserModelParams> =
    {
        title: "deepSeekModelsParameters",
        type: "object",
        properties: {
            modelName: { type: "string" },
            temperature: { type: "number" },
            apiKey: { type: "string" },
            ...(userModelParamsSchema.properties as PropertiesSchema<UserModelParams>),
        },
        required: ["modelId", "modelName", "temperature", "apiKey"],
        additionalProperties: false,
    };
