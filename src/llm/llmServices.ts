import { GrazieService } from "./llmServices/grazie/grazieService";
import { LLMService } from "./llmServices/llmService";
import { LMStudioService } from "./llmServices/lmStudio/lmStudioService";
import { OpenAiService } from "./llmServices/openai/openAiService";
import { PredefinedProofsService } from "./llmServices/predefinedProofs/predefinedProofsService";

export interface LLMServices {
    predefinedProofsService: PredefinedProofsService;
    openAiService: OpenAiService;
    grazieService: GrazieService;
    lmStudioService: LMStudioService;
}

export function disposeServices(llmServices: LLMServices) {
    asLLMServices(llmServices).forEach((service) => service.dispose());
}

export function asLLMServices(llmServices: LLMServices): LLMService[] {
    return [
        llmServices.predefinedProofsService,
        llmServices.openAiService,
        llmServices.grazieService,
        llmServices.lmStudioService,
    ];
}

export function switchByLLMServiceType<T>(
    llmService: LLMService,
    onPredefinedProofsService: () => T,
    onOpenAiService: () => T,
    onGrazieService: () => T,
    onLMStudioService: () => T
): T {
    if (llmService instanceof PredefinedProofsService) {
        return onPredefinedProofsService();
    } else if (llmService instanceof OpenAiService) {
        return onOpenAiService();
    } else if (llmService instanceof GrazieService) {
        return onGrazieService();
    } else if (llmService instanceof LMStudioService) {
        return onLMStudioService();
    } else {
        throw new Error(
            `switch by unknown LLMService: "${llmService.serviceName}"`
        );
    }
}
