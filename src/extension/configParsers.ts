import Ajv, { JSONSchemaType } from "ajv";
import { WorkspaceConfiguration, workspace } from "vscode";

import {
    GrazieUserModelParams,
    LMStudioUserModelParams,
    OpenAiUserModelParams,
    PredefinedProofsUserModelParams,
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

export function buildTheoremsRankerFromConfig(): ContextTheoremsRanker {
    const workspaceConfig = workspace.getConfiguration(pluginId);
    const rankerType = workspaceConfig.contextTheoremsRankerType;

    switch (rankerType) {
        case "distance":
            return new DistanceContextTheoremsRanker();
        case "random":
            return new RandomContextTheoremsRanker();
        default:
            throw new Error(
                `Unknown context theorems ranker type: ${rankerType}`
            );
    }
}

export class UserSettingsValidationError extends Error {
    constructor(
        message: string,
        public readonly settingsName: string
    ) {
        super(message);
    }

    toString(): string {
        return `Unable to validate user settings for ${this.settingsName}. Please refer to the README for the correct settings format: https://github.com/JetBrains-Research/coqpilot/blob/main/README.md#guide-to-model-configuration.`;
    }
}

export function parseUserModelsParams(
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
        throw new UserSettingsValidationError(
            `Unable to validate json against the class: ${JSON.stringify(validate.errors)}`,
            targetClassSchema.title ?? "Unknown"
        );
    }

    return instance;
}
