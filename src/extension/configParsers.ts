import Ajv, { JSONSchemaType } from "ajv";
import { WorkspaceConfiguration, commands, workspace } from "vscode";

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
import { UIMessageSeverity, showMessageToUser } from "./editorMessages";

export class SettingsValidationError extends Error {
    constructor(
        errorMessage: string,
        private readonly messageToShowToUser: string,
        private readonly settingToOpenName: string = pluginId,
        private readonly severity: UIMessageSeverity = "error"
    ) {
        super(errorMessage);
    }

    private static readonly openSettingsItem = "Open settings";

    showAsMessageToUser() {
        showMessageToUser(
            this.messageToShowToUser,
            this.severity,
            SettingsValidationError.openSettingsItem
        ).then((value) => {
            if (value === SettingsValidationError.openSettingsItem) {
                commands.executeCommand(
                    "workbench.action.openSettings",
                    this.settingToOpenName
                );
            }
        });
    }
}

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
                `Unknown context theorems ranker type: ${rankerType}`,
                `Please select one of the existing theorems-ranker types: "distance" or "random".`,
                "contextTheoremsRankerType"
            );
    }
}

export function parseAndValidateUserModelsParams(
    config: WorkspaceConfiguration,
    jsonSchemaValidator: Ajv
): UserModelsParams {
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
    const predefinedProofsParams: PredefinedProofsUserModelParams[] =
        config.predefinedProofsModelsParameters.map((params: any) =>
            validateAndParseJson(
                params,
                predefinedProofsUserModelParamsSchema,
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

    validateIdsAreUnique([
        ...openAiParams,
        ...grazieParams,
        ...predefinedProofsParams,
        ...lmStudioParams,
    ]);

    validateApiKeysAreProvided(openAiParams, grazieParams);

    return {
        openAiParams: openAiParams,
        grazieParams: grazieParams,
        predefinedProofsModelParams: predefinedProofsParams,
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
            throw new Error(
                `unknown \`targetClassSchema\`: "${targetClassSchema}"; while resolving json: "${json}"`
            );
        }
        throw new SettingsValidationError(
            `Unable to validate json against the class: ${JSON.stringify(validate.errors)}`,
            `Unable to validate user settings for \`${settingsName}\`. Please refer to the README for the correct settings format: https://github.com/JetBrains-Research/coqpilot/blob/main/README.md#guide-to-model-configuration.`,
            settingsName
        );
    }
    return instance;
}

function validateIdsAreUnique(modelsParams: UserModelParams[]) {
    const modelIds = modelsParams.map((params) => params.modelId);
    const uniqueModelIds = new Set<string>();
    for (const modelId of modelIds) {
        if (uniqueModelIds.has(modelId)) {
            throw new SettingsValidationError(
                `Models' identifiers are not unique: several models have \`modelId: "${modelId}"\``,
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
            `At least one of the ${serviceName} models has \`apiKey: "None"\``,
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
