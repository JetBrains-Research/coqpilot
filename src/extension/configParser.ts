import Ajv, { JSONSchemaType } from "ajv";
import { WorkspaceConfiguration, workspace } from "vscode";

import {
    GrazieUserModelParams,
    LMStudioUserModelParams,
    OpenAiUserModelParams,
    PredefinedProofsUserModelParams,
    UserModelParams,
    UserModelsParams,
    grazieUserModelParamsSchema,
    lmStudioUserModelParamsSchema,
    openAiUserModelParamsSchema,
    predefinedProofsUserModelParamsSchema,
} from "../llm/userModelParams";

import { ContextTheoremsRanker } from "../core/contextTheoremRanker/contextTheoremsRanker";
import { DistanceContextTheoremsRanker } from "../core/contextTheoremRanker/distanceContextTheoremsRanker";
import { RandomContextTheoremsRanker } from "../core/contextTheoremRanker/randomContextTheoremsRanker";

import { pluginId } from "./coqPilot";
import { SettingsValidationError } from "./settingsValidationError";

export function buildTheoremsRankerFromConfig(): ContextTheoremsRanker {
    const workspaceConfig = workspace.getConfiguration(pluginId);
    const rankerType = workspaceConfig.contextTheoremsRankerType;
    switch (rankerType) {
        case "distance":
            return new DistanceContextTheoremsRanker();
        case "random":
            return new RandomContextTheoremsRanker();
        default:
            throw new SettingsValidationError(
                `unknown context theorems ranker type: ${rankerType}`,
                `Please select one of the existing theorems-ranker types: "distance" or "random".`,
                "contextTheoremsRankerType"
            );
    }
}

export function parseAndValidateUserModelsParams(
    config: WorkspaceConfiguration,
    jsonSchemaValidator: Ajv
): UserModelsParams {
    const predefinedProofsParams: PredefinedProofsUserModelParams[] =
        config.predefinedProofsModelsParameters.map((params: any) =>
            validateAndParseJson(
                params,
                predefinedProofsUserModelParamsSchema,
                jsonSchemaValidator
            )
        );
    const openAiParams: OpenAiUserModelParams[] =
        config.openAiModelsParameters.map((params: any) =>
            validateAndParseJson(
                params,
                openAiUserModelParamsSchema,
                jsonSchemaValidator
            )
        );
    const grazieParams: GrazieUserModelParams[] =
        config.grazieModelsParameters.map((params: any) =>
            validateAndParseJson(
                params,
                grazieUserModelParamsSchema,
                jsonSchemaValidator
            )
        );
    const lmStudioParams: LMStudioUserModelParams[] =
        config.lmStudioModelsParameters.map((params: any) =>
            validateAndParseJson(
                params,
                lmStudioUserModelParamsSchema,
                jsonSchemaValidator
            )
        );
    const allModels = [
        ...predefinedProofsParams,
        ...openAiParams,
        ...grazieParams,
        ...lmStudioParams,
    ];

    validateModelsArePresent(allModels);
    validateIdsAreUnique(allModels);
    validateApiKeysAreProvided(openAiParams, grazieParams);

    return {
        predefinedProofsModelParams: predefinedProofsParams,
        openAiParams: openAiParams,
        grazieParams: grazieParams,
        lmStudioParams: lmStudioParams,
    };
}

function validateAndParseJson<T>(
    json: any,
    targetClassSchema: JSONSchemaType<T>,
    jsonSchemaValidator: Ajv
): T {
    const instance: T = json as T;
    const validate = jsonSchemaValidator.compile(targetClassSchema);
    if (!validate(instance)) {
        const settingsName = targetClassSchema.title;
        if (settingsName === undefined) {
            throw Error(
                `unknown \`targetClassSchema\`: "${targetClassSchema}"; while resolving json: "${json}"`
            );
        }
        console.log(`${JSON.stringify(json)} does not match the schema for \`${settingsName}\`.`);
        throw new SettingsValidationError(
            `unable to validate json against the class: ${JSON.stringify(validate.errors)}`,
            `Unable to validate user settings for \`${settingsName}\`. Please refer to the README for the correct settings format: https://github.com/JetBrains-Research/coqpilot/blob/main/README.md#guide-to-model-configuration.`,
            settingsName
        );
    }
    return instance;
}

function validateModelsArePresent(modelsParams: UserModelParams[]) {
    if (modelsParams.length === 0) {
        throw new SettingsValidationError(
            "no models specified for proof generation",
            "No models are chosen. Please specify at least one in the settings.",
            pluginId,
            "warning"
        );
    }
}

function validateIdsAreUnique(modelsParams: UserModelParams[]) {
    const modelIds = modelsParams.map((params) => params.modelId);
    const uniqueModelIds = new Set<string>();
    for (const modelId of modelIds) {
        if (uniqueModelIds.has(modelId)) {
            throw new SettingsValidationError(
                `models' identifiers are not unique: several models have \`modelId: "${modelId}"\``,
                `Please make identifiers of the models unique ("${modelId}" is not unique).`
            );
        } else {
            uniqueModelIds.add(modelId);
        }
    }
}

function validateApiKeysAreProvided(
    openAiParams: OpenAiUserModelParams[],
    grazieParams: GrazieUserModelParams[]
) {
    const buildApiKeyError = (
        serviceName: string,
        serviceSettingsName: string
    ) => {
        return new SettingsValidationError(
            `at least one of the ${serviceName} models has \`apiKey: "None"\``,
            `Please set your ${serviceName} API key in the settings.`,
            `${pluginId}.${serviceSettingsName}ModelsParameters`,
            "info"
        );
    };

    if (openAiParams.some((params) => params.apiKey === "None")) {
        throw buildApiKeyError("Open Ai", "openAi");
    }
    if (grazieParams.some((params) => params.apiKey === "None")) {
        throw buildApiKeyError("Grazie", "grazie");
    }
}
