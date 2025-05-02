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

export type RangoModelMode = "local" | "remote" | "mockOpenAI";

export interface RangoModelParams extends ModelParams {
    mode: RangoModelMode;
    timeoutSeconds: number;

    /**
     * Available only in the `local` mode.
     *
     * A path to the Rango's model checkpoint to execute locally.
     * In case of the relative path, it will be resolved from the installed Rango repository root.
     */
    localCheckpointPath: string;

    /**
     * Available only in the `remote` mode.
     *
     * A number of a port mapped by the SSH to the remote server serving the model.
     */
    mappedToRemotePort: number;

    /**
     * Available only in the `mockOpenAI` mode.
     *
     * A key to the OpenAI API.
     */
    mockOpenAIApiKey: string;

    /**
     * If set to true, all Coq source files located inside the project directory
     * will be parsed into data points by Rango (so to be used to form the context further).
     *
     * Otherwise, only the aux file for the one containing the proof target will be parsed.
     */
    enableWholeProjectDataPoints: boolean;

    /**
     * The directory to be used as the Rango's proof generation data location.
     *
     * If the expected directories structure is not present inside
     * (`repos/target_project` as a symlink to the target project, `data_points/` folder and `sentences.db`),
     * it will be initialized.
     *
     * Basically, this parameter makes it possible to "cache" the built data points
     * and the sentences database for the further executions.
     *
     * The path specified should be an absolute path.
     */
    dataLocDirectoryPath: string;
}

export interface ModelsParams {
    predefinedProofsModelParams: PredefinedProofsModelParams[];
    openAiParams: OpenAiModelParams[];
    grazieParams: GrazieModelParams[];
    lmStudioParams: LMStudioModelParams[];
    deepSeekParams: DeepSeekModelParams[];
    rangoParams: RangoModelParams[];
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

export const rangoModelParamsSchema: JSONSchemaType<RangoModelParams> = {
    title: "rangoModelsParameters",
    type: "object",
    properties: {
        mode: { type: "string", enum: ["local", "remote", "mockOpenAI"] },
        timeoutSeconds: { type: "number" },
        localCheckpointPath: { type: "string" },
        mappedToRemotePort: { type: "number" },
        mockOpenAIApiKey: { type: "string" },
        enableWholeProjectDataPoints: { type: "boolean" },
        dataLocDirectoryPath: { type: "string" },
        ...(modelParamsSchema.properties as PropertiesSchema<ModelParams>),
    },
    required: [
        "mode",
        "timeoutSeconds",
        "localCheckpointPath",
        "mappedToRemotePort",
        "mockOpenAIApiKey",
        "enableWholeProjectDataPoints",
        "dataLocDirectoryPath",
        ...modelParamsSchema.required,
    ],
    additionalProperties: false,
};
