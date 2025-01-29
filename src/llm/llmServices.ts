import { illegalState } from "../utils/throwErrors";

import { DeepSeekService } from "./llmServices/deepSeek/deepSeekService";
import { GrazieService } from "./llmServices/grazie/grazieService";
import { LLMService } from "./llmServices/llmService";
import { LMStudioService } from "./llmServices/lmStudio/lmStudioService";
import { ModelParams } from "./llmServices/modelParams";
import { OpenAiService } from "./llmServices/openai/openAiService";
import { PredefinedProofsService } from "./llmServices/predefinedProofs/predefinedProofsService";
import { UserModelParams } from "./userModelParams";

export interface LLMServices {
    predefinedProofsService: PredefinedProofsService;
    openAiService: OpenAiService;
    grazieService: GrazieService;
    lmStudioService: LMStudioService;
    deepSeekService: DeepSeekService;
}

export function disposeServices(llmServices: LLMServices) {
    asLLMServices(llmServices).forEach((service) => service.dispose());
}

export function asLLMServices(
    llmServices: LLMServices
): LLMService<UserModelParams, ModelParams>[] {
    return [
        llmServices.predefinedProofsService,
        llmServices.openAiService,
        llmServices.grazieService,
        llmServices.lmStudioService,
        llmServices.deepSeekService,
    ];
}

export function switchByLLMServiceType<T>(
    llmService: LLMService<any, any>,
    onPredefinedProofsService: () => T,
    onOpenAiService: () => T,
    onGrazieService: () => T,
    onLMStudioService: () => T,
    onDeepSeekService: () => T
): T {
    if (llmService instanceof PredefinedProofsService) {
        return onPredefinedProofsService();
    } else if (llmService instanceof OpenAiService) {
        return onOpenAiService();
    } else if (llmService instanceof GrazieService) {
        return onGrazieService();
    } else if (llmService instanceof LMStudioService) {
        return onLMStudioService();
    } else if (llmService instanceof DeepSeekService) {
        return onDeepSeekService();
    } else {
        illegalState(
            `switch by unknown \`LLMService\`: "${llmService.serviceName}"`
        );
    }
}
