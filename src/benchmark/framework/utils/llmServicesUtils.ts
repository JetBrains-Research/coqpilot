import { GrazieModelParamsResolver } from "../../../llm/llmServices/grazie/grazieModelParamsResolver";
import { GrazieService } from "../../../llm/llmServices/grazie/grazieService";
import { LLMService } from "../../../llm/llmServices/llmService";
import { LMStudioModelParamsResolver } from "../../../llm/llmServices/lmStudio/lmStudioModelParamsResolver";
import { LMStudioService } from "../../../llm/llmServices/lmStudio/lmStudioService";
import { ModelParams } from "../../../llm/llmServices/modelParams";
import { OpenAiModelParamsResolver } from "../../../llm/llmServices/openai/openAiModelParamsResolver";
import { OpenAiService } from "../../../llm/llmServices/openai/openAiService";
import { PredefinedProofsModelParamsResolver } from "../../../llm/llmServices/predefinedProofs/predefinedProofsModelParamsResolver";
import { PredefinedProofsService } from "../../../llm/llmServices/predefinedProofs/predefinedProofsService";
import { ParamsResolverImpl } from "../../../llm/llmServices/utils/paramsResolvers/paramsResolverImpl";
import { UserModelParams } from "../../../llm/userModelParams";

import { EventLogger } from "../../../logging/eventLogger";
import { LLMServiceIdentifier } from "../structures/llmServiceIdentifier";

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
    }
}

export type LLMServiceBuilder = () => [LLMService<any, any>, EventLogger];

export function selectLLMServiceBuilder(
    identifier: LLMServiceIdentifier
): LLMServiceBuilder {
    let createService: (eventLogger: EventLogger) => LLMService<any, any>;
    switch (identifier) {
        case LLMServiceIdentifier.PREDEFINED_PROOFS:
            createService = (eventLogger) =>
                new PredefinedProofsService(eventLogger);
            break;
        case LLMServiceIdentifier.OPENAI:
            createService = (eventLogger) => new OpenAiService(eventLogger);
            break;
        case LLMServiceIdentifier.GRAZIE:
            createService = (eventLogger) => new GrazieService(eventLogger);
            break;
        case LLMServiceIdentifier.LMSTUDIO:
            createService = (eventLogger) => new LMStudioService(eventLogger);
            break;
    }
    return () => {
        const eventLogger = new EventLogger();
        return [createService(eventLogger), eventLogger];
    };
}

export interface LLMServicesParamsResolvers {
    predefinedProofsModelParamsResolver: PredefinedProofsModelParamsResolver;
    openAiModelParamsResolver: OpenAiModelParamsResolver;
    grazieModelParamsResolver: GrazieModelParamsResolver;
    lmStudioModelParamsResolver: LMStudioModelParamsResolver;
}

export function createParamsResolvers(): LLMServicesParamsResolvers {
    return {
        predefinedProofsModelParamsResolver:
            new PredefinedProofsModelParamsResolver(),
        openAiModelParamsResolver: new OpenAiModelParamsResolver(),
        grazieModelParamsResolver: new GrazieModelParamsResolver(),
        lmStudioModelParamsResolver: new LMStudioModelParamsResolver(),
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
    }
}
