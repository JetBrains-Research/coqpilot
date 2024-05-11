import Ajv, { JSONSchemaType } from "ajv";
import { WorkspaceConfiguration, workspace } from "vscode";

import { LLMServices } from "../llm/llmServices";
import { LLMService } from "../llm/llmServices/llmService";
import { ModelParams, ModelsParams } from "../llm/llmServices/modelParams";
import { SingleParamResolutionResult } from "../llm/llmServices/utils/singleParamResolver";
import {
    GrazieUserModelParams,
    LMStudioUserModelParams,
    OpenAiUserModelParams,
    PredefinedProofsUserModelParams,
    UserModelParams,
    grazieUserModelParamsSchema,
    lmStudioUserModelParamsSchema,
    openAiUserModelParamsSchema,
    predefinedProofsUserModelParamsSchema,
} from "../llm/userModelParams";

import { ContextTheoremsRanker } from "../core/contextTheoremRanker/contextTheoremsRanker";
import { DistanceContextTheoremsRanker } from "../core/contextTheoremRanker/distanceContextTheoremsRanker";
import { RandomContextTheoremsRanker } from "../core/contextTheoremRanker/randomContextTheoremsRanker";

import { pluginId } from "./coqPilot";
import { EditorMessages } from "./editorMessages";
import {
    SettingsValidationError,
    showMessageToUserWithSettingsHint,
    toSettingName,
} from "./settingsValidationError";

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
    jsonSchemaValidator: Ajv,
    llmServices: LLMServices
): ModelsParams {
    const predefinedProofsUserParams: PredefinedProofsUserModelParams[] =
        config.predefinedProofsModelsParameters.map((params: any) =>
            validateAndParseJson(
                params,
                predefinedProofsUserModelParamsSchema,
                jsonSchemaValidator
            )
        );
    const openAiUserParams: OpenAiUserModelParams[] =
        config.openAiModelsParameters.map((params: any) =>
            validateAndParseJson(
                params,
                openAiUserModelParamsSchema,
                jsonSchemaValidator
            )
        );
    const grazieUserParams: GrazieUserModelParams[] =
        config.grazieModelsParameters.map((params: any) =>
            validateAndParseJson(
                params,
                grazieUserModelParamsSchema,
                jsonSchemaValidator
            )
        );
    const lmStudioUserParams: LMStudioUserModelParams[] =
        config.lmStudioModelsParameters.map((params: any) =>
            validateAndParseJson(
                params,
                lmStudioUserModelParamsSchema,
                jsonSchemaValidator
            )
        );

    validateIdsAreUnique([
        ...predefinedProofsUserParams,
        ...openAiUserParams,
        ...grazieUserParams,
        ...lmStudioUserParams,
    ]);
    validateApiKeysAreProvided(openAiUserParams, grazieUserParams);

    const modelsParams: ModelsParams = {
        predefinedProofsModelParams: resolveParamsAndShowResolutionLogs(
            llmServices.predefinedProofsService,
            predefinedProofsUserParams
        ),
        openAiParams: resolveParamsAndShowResolutionLogs(
            llmServices.openAiService,
            openAiUserParams
        ),
        grazieParams: resolveParamsAndShowResolutionLogs(
            llmServices.grazieService,
            grazieUserParams
        ),
        lmStudioParams: resolveParamsAndShowResolutionLogs(
            llmServices.lmStudioService,
            lmStudioUserParams
        ),
    };

    validateModelsArePresent([
        ...modelsParams.predefinedProofsModelParams,
        ...modelsParams.openAiParams,
        ...modelsParams.grazieParams,
        ...modelsParams.lmStudioParams,
    ]);

    return modelsParams;
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
        throw new SettingsValidationError(
            `unable to validate json against the class: ${JSON.stringify(validate.errors)}`,
            `Unable to validate user settings for \`${settingsName}\`. Please refer to the README for the correct settings format: https://github.com/JetBrains-Research/coqpilot/blob/main/README.md#guide-to-model-configuration.`,
            settingsName
        );
    }
    return instance;
}

function validateIdsAreUnique(allModels: UserModelParams[]) {
    const modelIds = allModels.map((params) => params.modelId);
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
    openAiUserParams: OpenAiUserModelParams[],
    grazieUserParams: GrazieUserModelParams[]
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

    if (openAiUserParams.some((params) => params.apiKey === "None")) {
        throw buildApiKeyError("Open Ai", "openAi");
    }
    if (grazieUserParams.some((params) => params.apiKey === "None")) {
        throw buildApiKeyError("Grazie", "grazie");
    }
}

function validateModelsArePresent<T>(allModels: T[]) {
    if (allModels.length === 0) {
        throw new SettingsValidationError(
            "no models specified for proof generation",
            "No models are chosen. Please specify at least one in the settings.",
            pluginId,
            "warning"
        );
    }
}

function resolveParamsAndShowResolutionLogs<
    InputModelParams extends UserModelParams,
    ResolvedModelParams extends ModelParams,
>(
    llmService: LLMService<InputModelParams, ResolvedModelParams>,
    inputParamsList: InputModelParams[]
): ResolvedModelParams[] {
    const settingName = toSettingName(llmService);
    const resolvedParamsList: ResolvedModelParams[] = [];

    for (const inputParams of inputParamsList) {
        const resolutionResult = llmService.resolveParameters(inputParams);

        // notify user about errors (with full logs for failed parameters) and overrides
        for (const paramLog of resolutionResult.resolutionLogs) {
            if (paramLog.resultValue === undefined) {
                // failed to resolve parameter
                const resolutionHistory = buildResolutionHistory(paramLog);
                showMessageToUserWithSettingsHint(
                    EditorMessages.modelConfiguredIncorrectly(
                        inputParams.modelId,
                        `${paramLog.isInvalidCause}${resolutionHistory}`
                    ),
                    "error",
                    settingName
                );
            } else if (paramLog.overriden.wasPerformed) {
                // resolved parameter, but it was overriden
                showMessageToUserWithSettingsHint(
                    buildParameterOverridenMessage(
                        inputParams.modelId,
                        paramLog
                    ),
                    "info",
                    settingName
                );
            }
        }

        if (resolutionResult.resolvedParams !== undefined) {
            resolvedParamsList.push(resolutionResult.resolvedParams);
        }
    }
    return resolvedParamsList;
}

function buildResolutionHistory(
    paramLog: SingleParamResolutionResult<any>
): string {
    const inputRead = paramLog.inputReadCorrectly.wasPerformed
        ? `read "${paramLog.inputReadCorrectly.withValue}"`
        : "";
    const withOverride = paramLog.overriden.wasPerformed
        ? `, overriden with ${paramLog.overriden.withValue}`
        : "";
    const withDefault = paramLog.resolvedWithDefault.wasPerformed
        ? `, resolved with default "${paramLog.resolvedWithDefault.withValue}"`
        : "";
    return paramLog.inputReadCorrectly.wasPerformed
        ? `; value's resolution: ${inputRead}${withOverride}${withDefault}`
        : "";
}

function buildParameterOverridenMessage(
    modelId: string,
    paramLog: SingleParamResolutionResult<any>
): string {
    const paramName = `\`${paramLog.inputParamName}\``;
    const withValue = `"${paramLog.overriden.withValue}"`;
    const explanation =
        paramLog.overriden.message === undefined
            ? ""
            : `: ${paramLog.overriden.message}`;
    return `The ${paramName} parameter of the "${modelId}" model was overriden with the value ${withValue}${explanation}. Please configure it the same way in the settings.`;
}
