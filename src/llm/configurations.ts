import {
    OpenAiModelParams,
    GrazieModelParams,
    PredefinedProofsModelParams,
    LmStudioModelParams,
} from "./llmServices/modelParamsInterfaces";
import { GrazieService } from "./llmServices/grazie/grazieService";
import { OpenAiService } from "./llmServices/openai/openAiService";
import { PredefinedProofsService } from "./llmServices/predefinedProofs/predefinedProofsService";
import { LmStudioService } from "./llmServices/lmStudio/lmStudioService";

export interface LLMServices {
    openAiService: OpenAiService;
    grazieService: GrazieService;
    predefinedProofsService: PredefinedProofsService;
    lmStudioService: LmStudioService;
}

export interface ModelsParams {
    openAiParams: OpenAiModelParams[];
    grazieParams: GrazieModelParams[];
    predefinedProofsModelParams: PredefinedProofsModelParams[];
    lmStudioModelParams: LmStudioModelParams[];
}
