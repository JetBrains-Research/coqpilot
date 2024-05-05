import { GrazieService } from "./llmServices/grazie/grazieService";
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
