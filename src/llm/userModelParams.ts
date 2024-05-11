import { JSONSchemaType } from "ajv";
import { PropertiesSchema } from "ajv/dist/types/json-schema";

export interface UserMultiroundProfile {
    // cannot be overriden: proof will always be updated no more than `maxRoundsNumber` times
    maxRoundsNumber?: number;

    // can be overriden in the `fixProof` call with the `choices` parameter
    proofFixChoices?: number;

    // use `${diagnostic}` syntax to include a diagnostic message into the prompt
    proofFixPrompt?: string;
}

export interface UserModelParams {
    modelName: string;
    choices?: number;

    systemPrompt?: string;

    newMessageMaxTokens?: number;
    tokensLimit?: number;

    multiroundProfile?: UserMultiroundProfile;
}

export interface OpenAiUserModelParams extends UserModelParams {
    temperature: number;
    apiKey: string;
}

export interface GrazieUserModelParams extends UserModelParams {
    apiKey: string;
}

export interface PredefinedProofsUserModelParams extends UserModelParams {
    // A list of tactics to try to solve the goal with.
    tactics: string[];
}

export interface LMStudioUserModelParams extends UserModelParams {
    temperature: number;
    port: number;
}

export interface UserModelsParams {
    openAiParams: OpenAiUserModelParams[];
    grazieParams: GrazieUserModelParams[];
    predefinedProofsModelParams: PredefinedProofsUserModelParams[];
    lmStudioParams: LMStudioUserModelParams[];
}

export const userMultiroundProfileSchema: JSONSchemaType<UserMultiroundProfile> =
    {
        type: "object",
        properties: {
            maxRoundsNumber: { type: "number", nullable: true },
            proofFixChoices: { type: "number", nullable: true },
            proofFixPrompt: { type: "string", nullable: true },
        },
        required: [],
        additionalProperties: false,
    };

export const userModelParamsSchema: JSONSchemaType<UserModelParams> = {
    type: "object",
    properties: {
        modelName: { type: "string" },
        choices: { type: "number", nullable: true },

        systemPrompt: { type: "string", nullable: true },

        newMessageMaxTokens: { type: "number", nullable: true },
        tokensLimit: { type: "number", nullable: true },

        multiroundProfile: {
            type: "object",
            oneOf: [userMultiroundProfileSchema],
            nullable: true,
        },
    },
    required: ["modelName"],
};

export const openAiUserModelParamsSchema: JSONSchemaType<OpenAiUserModelParams> =
    {
        title: "openAiModelsParameters",
        type: "object",
        properties: {
            temperature: { type: "number" },
            apiKey: { type: "string" },
            ...(userModelParamsSchema.properties as PropertiesSchema<UserModelParams>),
        },
        required: ["modelName", "temperature", "apiKey"],
    };

export const grazieUserModelParamsSchema: JSONSchemaType<GrazieUserModelParams> =
    {
        title: "grazieModelsParameters",
        type: "object",
        properties: {
            apiKey: { type: "string" },
            ...(userModelParamsSchema.properties as PropertiesSchema<UserModelParams>),
        },
        required: ["modelName", "apiKey"],
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
        required: ["modelName", "tactics"],
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
        required: ["modelName", "temperature", "port"],
    };
