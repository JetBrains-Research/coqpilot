import { ErrorsHandlingMode } from "../../../../llm/llmServices/commonStructures/errorsHandlingMode";
import { DeepSeekModelParamsResolver } from "../../../../llm/llmServices/deepSeek/deepSeekModelParamsResolver";
import { DeepSeekService } from "../../../../llm/llmServices/deepSeek/deepSeekService";
import { GrazieModelParamsResolver } from "../../../../llm/llmServices/grazie/grazieModelParamsResolver";
import { GrazieService } from "../../../../llm/llmServices/grazie/grazieService";
import { LLMService } from "../../../../llm/llmServices/llmService";
import { LMStudioModelParamsResolver } from "../../../../llm/llmServices/lmStudio/lmStudioModelParamsResolver";
import { LMStudioService } from "../../../../llm/llmServices/lmStudio/lmStudioService";
import { ModelParams } from "../../../../llm/llmServices/modelParams";
import { OpenAiModelParamsResolver } from "../../../../llm/llmServices/openai/openAiModelParamsResolver";
import { OpenAiService } from "../../../../llm/llmServices/openai/openAiService";
import { PredefinedProofsModelParamsResolver } from "../../../../llm/llmServices/predefinedProofs/predefinedProofsModelParamsResolver";
import { PredefinedProofsService } from "../../../../llm/llmServices/predefinedProofs/predefinedProofsService";
import { ParamsResolverImpl } from "../../../../llm/llmServices/utils/paramsResolvers/paramsResolverImpl";
import { UserModelParams } from "../../../../llm/userModelParams";

import { EventLogger } from "../../../../logging/eventLogger";
import { LLMServiceIdentifier } from "../../structures/common/llmServiceIdentifier";

/**
 * Regardless of the string values defined in the implementation of `LLMServiceIdentifier` (they can change with time),
 * this function guarantees to provide nice and human-readable names of the services.
 */
export function getShortName(identifier: LLMServiceIdentifier): string {
    switch (identifier) {
        case LLMServiceIdentifier.PREDEFINED_PROOFS:
            return "Predefined Proofs";
        case LLMServiceIdentifier.OPENAI:
            return "Open AI";
        case LLMServiceIdentifier.GRAZIE:
            return "Grazie";
        case LLMServiceIdentifier.LMSTUDIO:
            return "LM Studio";
        case LLMServiceIdentifier.DEEPSEEK:
            return "DeepSeek";
    }
}

export type LLMServiceBuilder = (
    eventLogger: EventLogger | undefined,
    errorsHandlingMode: ErrorsHandlingMode
) => LLMService<UserModelParams, ModelParams>;

export function selectLLMServiceBuilder(
    identifier: LLMServiceIdentifier
): LLMServiceBuilder {
    switch (identifier) {
        case LLMServiceIdentifier.PREDEFINED_PROOFS:
            return (eventLogger, errorsHandlingMode) =>
                new PredefinedProofsService(eventLogger, errorsHandlingMode);
        case LLMServiceIdentifier.OPENAI:
            return (eventLogger, errorsHandlingMode) =>
                new OpenAiService(eventLogger, errorsHandlingMode);
        case LLMServiceIdentifier.GRAZIE:
            return (eventLogger, errorsHandlingMode) =>
                new GrazieService(eventLogger, errorsHandlingMode);
        case LLMServiceIdentifier.LMSTUDIO:
            return (eventLogger, errorsHandlingMode) =>
                new LMStudioService(eventLogger, errorsHandlingMode);
        case LLMServiceIdentifier.DEEPSEEK:
            return (eventLogger, errorsHandlingMode) =>
                new DeepSeekService(eventLogger, errorsHandlingMode);
    }
}

export interface LLMServicesParamsResolvers {
    predefinedProofsModelParamsResolver: PredefinedProofsModelParamsResolver;
    openAiModelParamsResolver: OpenAiModelParamsResolver;
    grazieModelParamsResolver: GrazieModelParamsResolver;
    lmStudioModelParamsResolver: LMStudioModelParamsResolver;
    deepSeekModelParamsResolver: DeepSeekModelParamsResolver;
}

export function createParamsResolvers(): LLMServicesParamsResolvers {
    return {
        predefinedProofsModelParamsResolver:
            new PredefinedProofsModelParamsResolver(),
        openAiModelParamsResolver: new OpenAiModelParamsResolver(),
        grazieModelParamsResolver: new GrazieModelParamsResolver(),
        lmStudioModelParamsResolver: new LMStudioModelParamsResolver(),
        deepSeekModelParamsResolver: new DeepSeekModelParamsResolver(),
    };
}

export function getParamsResolver(
    identifier: LLMServiceIdentifier,
    paramsResolvers: LLMServicesParamsResolvers
): ParamsResolverImpl<UserModelParams, ModelParams> {
    switch (identifier) {
        case LLMServiceIdentifier.PREDEFINED_PROOFS:
            return paramsResolvers.predefinedProofsModelParamsResolver;
        case LLMServiceIdentifier.OPENAI:
            return paramsResolvers.openAiModelParamsResolver;
        case LLMServiceIdentifier.GRAZIE:
            return paramsResolvers.grazieModelParamsResolver;
        case LLMServiceIdentifier.LMSTUDIO:
            return paramsResolvers.lmStudioModelParamsResolver;
        case LLMServiceIdentifier.DEEPSEEK:
            return paramsResolvers.deepSeekModelParamsResolver;
    }
}
