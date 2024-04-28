import { GrazieService } from "./llmServices/grazie/grazieService";
import { LMStudioService } from "./llmServices/lmStudio/lmStudioService";
import { OpenAiService } from "./llmServices/openai/openAiService";
import { PredefinedProofsService } from "./llmServices/predefinedProofs/predefinedProofsService";

export interface LLMServices {
    openAiService: OpenAiService;
    grazieService: GrazieService;
    predefinedProofsService: PredefinedProofsService;
    lmStudioService: LMStudioService;
}

export function disposeServices(services: LLMServices) {
    services.openAiService.dispose();
    services.grazieService.dispose();
    services.predefinedProofsService.dispose();
    services.lmStudioService.dispose();
}
