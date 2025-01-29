import Ajv, { DefinedError, JSONSchemaType } from "ajv";
import { WorkspaceConfiguration, workspace } from "vscode";

import { LLMServices } from "../../llm/llmServices";
import { LLMService } from "../../llm/llmServices/llmService";
import { ModelParams, ModelsParams } from "../../llm/llmServices/modelParams";
import { SingleParamResolutionResult } from "../../llm/llmServices/utils/paramsResolvers/abstractResolvers";
import {
    DeepSeekUserModelParams,
    GrazieUserModelParams,
    LMStudioUserModelParams,
    OpenAiUserModelParams,
    PredefinedProofsUserModelParams,
    UserModelParams,
    deepSeekUserModelParamsSchema,
    grazieUserModelParamsSchema,
    lmStudioUserModelParamsSchema,
    openAiUserModelParamsSchema,
    predefinedProofsUserModelParamsSchema,
} from "../../llm/userModelParams";

import { DistanceContextTheoremsRanker } from "../../core/contextTheoremRanker/actualRankers/distanceContextTheoremsRanker";
import { JaccardIndexContextTheoremsRanker } from "../../core/contextTheoremRanker/actualRankers/jaccardIndexContextTheoremsRanker";
import { RandomContextTheoremsRanker } from "../../core/contextTheoremRanker/actualRankers/randomContextTheoremsRanker";
import { ContextTheoremsRanker } from "../../core/contextTheoremRanker/contextTheoremsRanker";

import { AjvMode, buildAjv } from "../../utils/ajvErrorsHandling";
import { stringifyAnyValue, stringifyDefinedValue } from "../../utils/printers";
import { illegalState, throwError } from "../../utils/throwErrors";
import {
    EditorMessages,
    showMessageToUserWithSettingsHint,
} from "../ui/messages/editorMessages";
import { pluginId } from "../utils/pluginId";

import {
    SettingsValidationError,
    toSettingName,
} from "./settingsValidationError";

export function parseCoqLspServerPath(): string {
    const workspaceConfig = workspace.getConfiguration(pluginId);
    const coqLspServerPath = workspaceConfig.get("coqLspServerPath");
    if (typeof coqLspServerPath !== "string") {
        throwError("`coqLspServerPath` is not properly configured");
    }
    return coqLspServerPath;
}

export function buildTheoremsRankerFromConfig(): ContextTheoremsRanker {
    const workspaceConfig = workspace.getConfiguration(pluginId);
    const rankerType = workspaceConfig.contextTheoremsRankerType;
    switch (rankerType) {
        case "distance":
            return new DistanceContextTheoremsRanker();
        case "random":
            return new RandomContextTheoremsRanker();
        case "jaccardIndex":
            return new JaccardIndexContextTheoremsRanker();
        default:
            throw new SettingsValidationError(
                `unknown context theorems ranker type: ${rankerType}`,
                EditorMessages.unknownContextTheoremsRanker,
                "contextTheoremsRankerType"
            );
    }
}

export function readAndValidateUserModelsParams(
    config: WorkspaceConfiguration,
    llmServices: LLMServices
): ModelsParams {
    /*
     * Although the messages might become too verbose because of reporting all errors at once
     * (unfortuantely, vscode notifications do not currently support formatting);
     * we want the user to fix type-validation issues as soon as possible
     * to move on to clearer messages and generating completions faster.
     */
    const jsonSchemaValidator = buildAjv(AjvMode.COLLECT_ALL_ERRORS);

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
    const deepSeekUserParams: DeepSeekUserModelParams[] =
        config.deepSeekModelsParameters.map((params: any) =>
            validateAndParseJson(
                params,
                deepSeekUserModelParamsSchema,
                jsonSchemaValidator
            )
        );

    validateIdsAreUnique([
        ...predefinedProofsUserParams,
        ...openAiUserParams,
        ...grazieUserParams,
        ...lmStudioUserParams,
        ...deepSeekUserParams,
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
        deepSeekParams: resolveParamsAndShowResolutionLogs(
            llmServices.deepSeekService,
            deepSeekUserParams
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
            illegalState(
                "specified `targetClassSchema` does not have `title`; ",
                `while resolving json: ${stringifyAnyValue(json)}`
            );
        }
        const ajvErrors = validate.errors as DefinedError[];
        if (ajvErrors === null || ajvErrors === undefined) {
            illegalState(
                "validation with Ajv failed, but `validate.errors` are not defined; ",
                `while resolving json: ${stringifyAnyValue(json)}`
            );
        }
        throw new SettingsValidationError(
            `unable to validate json ${stringifyAnyValue(json)}: ${stringifyDefinedValue(validate.errors)}`,
            EditorMessages.unableToValidateUserSettings(
                settingsName,
                ajvErrors,
                ["oneOf"] // ignore additional boilerplate "oneOf" error, which appears if something is wrong with nested `multiroundProfile`
            ),
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
                EditorMessages.modelsIdsAreNotUnique(modelId)
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
            EditorMessages.apiKeyIsNotSet(serviceName),
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
            EditorMessages.noValidModelsAreChosen,
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
            } else if (
                paramLog.overriden.wasPerformed &&
                paramLog.inputReadCorrectly.wasPerformed
            ) {
                // resolved parameter, but the user value was overriden
                showMessageToUserWithSettingsHint(
                    EditorMessages.userValueWasOverriden(
                        inputParams.modelId,
                        paramLog.inputParamName ?? "<undefined parameter>",
                        paramLog.overriden.withValue,
                        paramLog.overriden.message
                    ),
                    "info",
                    settingName
                );
            }
        }

        if (resolutionResult.resolved !== undefined) {
            resolvedParamsList.push(resolutionResult.resolved);
        }
    }
    return resolvedParamsList;
}

function buildResolutionHistory(
    paramLog: SingleParamResolutionResult<any>
): string {
    const inputReadPerformed = paramLog.inputReadCorrectly.wasPerformed;
    const overridePerformed = paramLog.overriden.wasPerformed;
    const withDefaultPerformed = paramLog.resolvedWithDefault.wasPerformed;

    const onlySuccessfulRead =
        inputReadPerformed && !overridePerformed && !withDefaultPerformed;
    if (onlySuccessfulRead) {
        return "";
    }
    const inputRead = paramLog.inputReadCorrectly.wasPerformed
        ? `read ${stringifyAnyValue(paramLog.inputReadCorrectly.withValue)}`
        : "no input value read";
    const withOverride = paramLog.overriden.wasPerformed
        ? `, overriden with ${stringifyAnyValue(paramLog.overriden.withValue)}`
        : "";
    const withDefault = paramLog.resolvedWithDefault.wasPerformed
        ? `, resolved with default ${stringifyAnyValue(paramLog.resolvedWithDefault.withValue)}`
        : "";

    const onlyFailedRead =
        !inputReadPerformed && !overridePerformed && !withDefaultPerformed;
    const anyResolutionActionPerformed =
        overridePerformed || withDefaultPerformed;
    return onlyFailedRead || anyResolutionActionPerformed
        ? `; value's resolution: ${inputRead}${withOverride}${withDefault}`
        : "";
}
