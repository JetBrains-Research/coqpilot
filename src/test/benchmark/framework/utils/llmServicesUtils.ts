import { GrazieService } from "../../../../llm/llmServices/grazie/grazieService";
import { LLMService } from "../../../../llm/llmServices/llmService";
import { LMStudioService } from "../../../../llm/llmServices/lmStudio/lmStudioService";
import { OpenAiService } from "../../../../llm/llmServices/openai/openAiService";
import { PredefinedProofsService } from "../../../../llm/llmServices/predefinedProofs/predefinedProofsService";

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
