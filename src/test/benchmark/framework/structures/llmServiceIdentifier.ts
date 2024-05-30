import { GrazieService } from "../../../../llm/llmServices/grazie/grazieService";
import { LLMService } from "../../../../llm/llmServices/llmService";
import { LMStudioService } from "../../../../llm/llmServices/lmStudio/lmStudioService";
import { OpenAiService } from "../../../../llm/llmServices/openai/openAiService";
import { PredefinedProofsService } from "../../../../llm/llmServices/predefinedProofs/predefinedProofsService";

import { EventLogger } from "../../../../logging/eventLogger";

export enum LLMServiceIdentifier {
    PREDEFINED_PROOFS,
    OPENAI,
    GRAZIE,
    LMSTUDIO,
}

export type LLMServiceBuilder = () => LLMService<any, any>;

// TODO: if more functions appear, put in a separate llmServicesUtils

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
