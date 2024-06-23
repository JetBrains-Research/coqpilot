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

export function getParamsResolver(
    identifier: LLMServiceIdentifier
): ParamsResolverImpl<UserModelParams, ModelParams> {
    switch (identifier) {
        case LLMServiceIdentifier.PREDEFINED_PROOFS:
            return new PredefinedProofsModelParamsResolver();
        case LLMServiceIdentifier.OPENAI:
            return new OpenAiModelParamsResolver();
        case LLMServiceIdentifier.GRAZIE:
            return new GrazieModelParamsResolver();
        case LLMServiceIdentifier.LMSTUDIO:
            return new LMStudioModelParamsResolver();
    }
}

export type LLMServiceBuilder = () => LLMService<any, any>;

export function selectLLMServiceBuilder(
    identifier: LLMServiceIdentifier
): LLMServiceBuilder {
    const eventLogger = new EventLogger();
    switch (identifier) {
        case LLMServiceIdentifier.PREDEFINED_PROOFS:
            return () => new PredefinedProofsService(eventLogger);
        case LLMServiceIdentifier.OPENAI:
            return () => new OpenAiService(eventLogger);
        case LLMServiceIdentifier.GRAZIE:
            return () => new GrazieService(eventLogger);
        case LLMServiceIdentifier.LMSTUDIO:
            return () => new LMStudioService(eventLogger);
    }
}
