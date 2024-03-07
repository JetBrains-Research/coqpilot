// import { JSONSchemaType } from "ajv";

export interface UserMultiroundProfile {
    // cannot be overriden: proof will always be updated no more than `maxRoundsNumber` times
    maxRoundsNumber?: number;

    // can be overriden in the `fixProof` call with the `choices` parameter
    proofFixChoices?: number;

    // use `${diagnostic}` syntax to include a diagnostic message into the promt
    proofFixPromt?: string;
}

export interface UserModelParams {
    modelName: string;
    choices: number;

    systemPromt?: string;

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

export interface UserModelsParams {
    openAiParams: OpenAiUserModelParams[];
    grazieParams: GrazieUserModelParams[];
    predefinedProofsModelParams: PredefinedProofsUserModelParams[];
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
