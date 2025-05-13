import Ajv, { DefinedError, JSONSchemaType } from "ajv";
import {
    ExtensionContext as VSCodeContext,
    WorkspaceConfiguration,
    workspace,
} from "vscode";

import {
    GenerationBundle,
    GenerationBundlesStorage,
    ResolvedGenerationBundles,
} from "../../llm/generationBundles";
import { LLMService } from "../../llm/llmServices/llmService";
import { LLMServiceIdentifier } from "../../llm/llmServices/llmServiceIdentifier";
import { ModelParams } from "../../llm/llmServices/modelParams";
import { buildParamsResolutionMessages } from "../../llm/llmServices/utils/paramsResolvers/kit/paramsResolutionAnalysis";
import { getShortName } from "../../llm/llmServices/utils/serialization/toLog";
import { LLMServicesStorage } from "../../llm/llmServicesStorage";
import {
    UserModelParams,
    deepSeekUserModelParamsSchema,
    grazieUserModelParamsSchema,
    lmStudioUserModelParamsSchema,
    openAiUserModelParamsSchema,
    predefinedProofsUserModelParamsSchema,
    rangoUserModelParamsSchema,
} from "../../llm/userModelParams";

import { DistanceContextTheoremsRanker } from "../../core/contextTheoremRanker/actualRankers/distanceContextTheoremsRanker";
import { JaccardIndexContextTheoremsRanker } from "../../core/contextTheoremRanker/actualRankers/jaccardIndexContextTheoremsRanker";
import { RandomContextTheoremsRanker } from "../../core/contextTheoremRanker/actualRankers/randomContextTheoremsRanker";
import { ContextTheoremsRanker } from "../../core/contextTheoremRanker/contextTheoremsRanker";

import { AjvMode, buildAjv } from "../../utils/ajvErrorsHandling";
import { findFirstDuplicate } from "../../utils/collectionUtils/listUtils";
import { groupByAndMap, mapValues } from "../../utils/collectionUtils/mapUtils";
import { illegalState, throwError } from "../../utils/errors/throwErrors";
import { stringifyAnyValue, stringifyDefinedValue } from "../../utils/printers";
import { UserInstallationInteractor } from "../installers/abstractUserInstallation";
import {
    EditorMessages,
    showMessageToUserWithSettingsHint,
} from "../ui/messages/editorMessages";
import { PLUGIN_ID } from "../utils/pluginId";

import { toSettingName } from "./settingsNames";
import { SettingsValidationError } from "./settingsValidationError";

export function parseCoqLspServerPath(): string {
    const workspaceConfig = workspace.getConfiguration(PLUGIN_ID);
    const coqLspServerPath = workspaceConfig.get("coqLspServerPath");
    if (typeof coqLspServerPath !== "string") {
        throwError("`coqLspServerPath` is not properly configured");
    }
    return coqLspServerPath;
}

export function buildTheoremsRankerFromConfig(): ContextTheoremsRanker {
    const workspaceConfig = workspace.getConfiguration(PLUGIN_ID);
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

export async function readAndValidateUserModelsParams(
    config: WorkspaceConfiguration,
    llmServices: LLMServicesStorage,
    vscodeContext: VSCodeContext
): Promise<ResolvedGenerationBundles> {
    const inputParamsWithIdentifiers = parseUserModelParams(config);
    const inputParamsByIdentifier: Map<
        LLMServiceIdentifier,
        UserModelParams[]
    > = mapValues(
        groupByAndMap(
            inputParamsWithIdentifiers,
            (item) => item.identifier,
            (item) => item.inputParams
        ),
        (_, params: UserModelParams[][]) => params.flat()
    );
    const allInputParams = inputParamsWithIdentifiers.flatMap(
        (item) => item.inputParams
    );

    const inputBundles = new GenerationBundlesStorage<UserModelParams>();
    for (const { inputParams, identifier } of inputParamsWithIdentifiers) {
        const servicesOfType = llmServices.getServices(identifier);
        for (const service of servicesOfType) {
            inputBundles.addBundle({
                llmService: service,
                models: inputParams,
            });
        }
    }

    await provideServicesInstallations(
        vscodeContext.extensionPath,
        inputBundles.allBundles()
    );

    validateIdsAreUnique(allInputParams);
    validateApiKeysAreProvided(inputParamsByIdentifier, [
        LLMServiceIdentifier.OPENAI,
        LLMServiceIdentifier.GRAZIE,
        LLMServiceIdentifier.DEEPSEEK,
        LLMServiceIdentifier.RANGO,
    ]);

    const resolvedBundles = new GenerationBundlesStorage<ModelParams>();
    for (const inputBundle of inputBundles.allBundles()) {
        const resolvedParams = resolveParamsAndShowResolutionLogs<
            UserModelParams,
            ModelParams
        >(inputBundle.llmService, inputBundle.models);
        resolvedBundles.addBundle({
            llmService: inputBundle.llmService,
            models: resolvedParams,
        });
    }
    validateModelsArePresent(resolvedBundles.allBundles());

    return resolvedBundles;
}

// TODO: skip service's models if the user declines its installation, don't throw
async function provideServicesInstallations(
    coqPilotPath: string,
    inputBundles: GenerationBundle<UserModelParams>[]
) {
    for (const { llmService, models } of inputBundles) {
        const installerProvider = llmService.installerProvider;
        if (installerProvider === undefined) {
            continue;
        }
        const { installer, options } = installerProvider();
        await installer.provideInstallationForRequest(
            models,
            coqPilotPath,
            undefined,
            options,
            new UserInstallationInteractor(installer)
        );
    }
}

function validateIdsAreUnique(allModels: UserModelParams[]) {
    const modelIds = allModels.map((params) => params.modelId);
    const duplicateModelId = findFirstDuplicate(modelIds);
    if (duplicateModelId !== undefined) {
        throw new SettingsValidationError(
            `models' identifiers are not unique: several models have \`modelId: "${duplicateModelId}"\``,
            EditorMessages.modelsIdsAreNotUnique(duplicateModelId)
        );
    }
}

function validateApiKeysAreProvided(
    inputParamsByIdentifier: Map<LLMServiceIdentifier, UserModelParams[]>,
    identifiersToValidate: LLMServiceIdentifier[]
) {
    function throwBuildApiKeyError(
        serviceName: string,
        serviceSettingsName: string
    ) {
        throw new SettingsValidationError(
            `at least one of the ${serviceName} models has \`apiKey: "None"\``,
            EditorMessages.apiKeyIsNotSet(serviceName),
            `${PLUGIN_ID}.${serviceSettingsName}ModelsParameters`,
            "info"
        );
    }

    function checkApiKeyIsNone(params: any): boolean {
        return params.apiKey === "None" || params.mockOpenAIApiKey === "None";
    }

    for (const identifier of identifiersToValidate) {
        const inputModels =
            inputParamsByIdentifier.get(LLMServiceIdentifier.GRAZIE) ?? [];
        if (inputModels.some(checkApiKeyIsNone)) {
            throwBuildApiKeyError(
                getShortName(identifier),
                toSettingName(identifier)
            );
        }
    }
}

function validateModelsArePresent<T>(allModels: T[]) {
    if (allModels.length === 0) {
        throw new SettingsValidationError(
            "no models specified for proof generation",
            EditorMessages.noValidModelsAreChosen,
            PLUGIN_ID,
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
    const settingName = toSettingName(llmService.identifier);
    const resolvedParamsList: ResolvedModelParams[] = [];

    for (const inputParams of inputParamsList) {
        const resolutionResult = llmService.resolveParameters(inputParams);
        const resolutionMessages = buildParamsResolutionMessages(
            resolutionResult,
            inputParams.modelId
        );
        if (resolutionMessages.invalidConfigurationMessage !== undefined) {
            showMessageToUserWithSettingsHint(
                EditorMessages.modelConfiguredIncorrectly(
                    inputParams.modelId,
                    resolutionMessages.invalidConfigurationMessage
                ),
                "error",
                settingName
            );
        } else if (resolutionMessages.warningMessage !== undefined) {
            showMessageToUserWithSettingsHint(
                resolutionMessages.warningMessage,
                "warning",
                settingName
            );
        }
        if (resolutionResult.resolved !== undefined) {
            resolvedParamsList.push(resolutionResult.resolved);
        }
    }
    return resolvedParamsList;
}

interface InputParamsWithIdentifier<T extends UserModelParams> {
    inputParams: T[];
    identifier: LLMServiceIdentifier;
}

function parseUserModelParams(
    config: WorkspaceConfiguration
): InputParamsWithIdentifier<UserModelParams>[] {
    /*
     * Although the messages might become too verbose because of reporting all errors at once
     * (unfortuantely, vscode notifications do not currently support formatting);
     * we want the user to fix type-validation issues as soon as possible
     * to move on to clearer messages and generating completions faster.
     */
    const jsonSchemaValidator = buildAjv(AjvMode.COLLECT_ALL_ERRORS);
    const inputParamsWithIdentifiers: InputParamsWithIdentifier<UserModelParams>[] =
        [
            {
                inputParams: config.predefinedProofsModelsParameters.map(
                    (params: any) =>
                        validateAndParseJson(
                            params,
                            predefinedProofsUserModelParamsSchema,
                            jsonSchemaValidator
                        )
                ),
                identifier: LLMServiceIdentifier.PREDEFINED_PROOFS,
            },
            {
                inputParams: config.openAiModelsParameters.map((params: any) =>
                    validateAndParseJson(
                        params,
                        openAiUserModelParamsSchema,
                        jsonSchemaValidator
                    )
                ),
                identifier: LLMServiceIdentifier.OPENAI,
            },
            {
                inputParams: config.grazieModelsParameters.map((params: any) =>
                    validateAndParseJson(
                        params,
                        grazieUserModelParamsSchema,
                        jsonSchemaValidator
                    )
                ),
                identifier: LLMServiceIdentifier.GRAZIE,
            },
            {
                inputParams: config.lmStudioModelsParameters.map(
                    (params: any) =>
                        validateAndParseJson(
                            params,
                            lmStudioUserModelParamsSchema,
                            jsonSchemaValidator
                        )
                ),
                identifier: LLMServiceIdentifier.LMSTUDIO,
            },
            {
                inputParams: config.deepSeekModelsParameters.map(
                    (params: any) =>
                        validateAndParseJson(
                            params,
                            deepSeekUserModelParamsSchema,
                            jsonSchemaValidator
                        )
                ),
                identifier: LLMServiceIdentifier.DEEPSEEK,
            },
            {
                inputParams: config.rangoModelsParameters.map((params: any) =>
                    validateAndParseJson(
                        params,
                        rangoUserModelParamsSchema,
                        jsonSchemaValidator
                    )
                ),
                identifier: LLMServiceIdentifier.RANGO,
            },
        ];
    return inputParamsWithIdentifiers;
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
