import { illegalState } from "../utils/errors/throwErrors";

import { DeepSeekService } from "./llmServices/deepSeek/deepSeekService";
import { GrazieService } from "./llmServices/grazie/grazieService";
import { LLMService } from "./llmServices/llmService";
import { LMStudioService } from "./llmServices/lmStudio/lmStudioService";
import { ModelParams } from "./llmServices/modelParams";
import { OpenAiService } from "./llmServices/openai/openAiService";
import { PredefinedProofsService } from "./llmServices/predefinedProofs/predefinedProofsService";
import { RangoService } from "./llmServices/rango/rangoService";
import { UserModelParams } from "./userModelParams";

export interface LLMServices {
    predefinedProofsService: PredefinedProofsService;
    openAiService: OpenAiService;
    grazieService: GrazieService;
    lmStudioService: LMStudioService;
    deepSeekService: DeepSeekService;
    rangoService: RangoService;
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
        llmServices.rangoService,
    ];
}

export function switchByLLMServiceType<T>(
    llmService: LLMService<any, any>,
    onPredefinedProofsService: () => T,
    onOpenAiService: () => T,
    onGrazieService: () => T,
    onLMStudioService: () => T,
    onDeepSeekService: () => T,
    onRangoService: () => T
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
    } else if (llmService instanceof RangoService) {
        return onRangoService();
    } else {
        illegalState(
            `switch by unknown \`LLMService\`: "${llmService.serviceName}"`
        );
    }
}
