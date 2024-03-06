// import { JSONSchemaType } from "ajv";

export interface UserModelParams {
    modelName: string;
    choices: number;

    systemPromt?: string;

    newMessageMaxTokens?: number;
    tokensLimit?: number;
}

export interface UserOpenAiModelParams extends UserModelParams {
    temperature: number;
    apiKey: string;
}

export interface UserGrazieModelParams extends UserModelParams {
    apiKey: string;
}

export interface UserPredefinedProofsModelParams extends UserModelParams {
    // A list of tactics to try to solve the goal with.
    tactics: string[];
}

// export const openAiModelParamsSchema: JSONSchemaType<OpenAiModelParams> = {
//     type: "object",
//     properties: {
//         prompt: { type: "string" },
//         answerMaxTokens: { type: "number" },
//         modelContextLength: { type: "number" },
//         temperature: { type: "number" },
//         model: { type: "string" },
//         apiKey: { type: "string" },
//         choices: { type: "number" },
//     },
//     required: [
//         "prompt",
//         "answerMaxTokens",
//         "modelContextLength",
//         "temperature",
//         "model",
//         "apiKey",
//         "choices",
//     ],
// };

// export const grazieModelParamsSchema: JSONSchemaType<GrazieModelParams> = {
//     type: "object",
//     properties: {
//         prompt: { type: "string" },
//         modelContextLength: { type: "number" },
//         model: { type: "string" },
//         apiKey: { type: "string" },
//         choices: { type: "number" },
//     },
//     required: ["prompt", "modelContextLength", "model", "apiKey", "choices"],
// };

// export const predefinedProofsModelParamsSchema: JSONSchemaType<PredefinedProofsModelParams> =
//     {
//         type: "object",
//         properties: {
//             tactics: {
//                 type: "array",
//                 items: { type: "string" },
//             },
//         },
//         required: ["tactics"],
//     };
