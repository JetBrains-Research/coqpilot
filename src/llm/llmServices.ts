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

export function disposeServices(services: LLMServices) {
    services.predefinedProofsService.dispose();
    services.openAiService.dispose();
    services.grazieService.dispose();
    services.lmStudioService.dispose();
}

export function asLLMServices(llmServices: LLMServices): LLMService[] {
    return [
        llmServices.predefinedProofsService,
        llmServices.openAiService,
        llmServices.grazieService,
        llmServices.lmStudioService,
    ];
}
