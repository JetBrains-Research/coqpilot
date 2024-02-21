import {
    OpenAiModelParams,
    GrazieModelParams,
    PredefinedProofsModelParams,
} from "./llmServices/modelParamsInterfaces";
import { GrazieService } from "./llmServices/grazie/grazieService";
import { OpenAiService } from "./llmServices/openai/openAiService";
import { PredefinedProofsService } from "./llmServices/predefinedProofs/predefinedProofsService";

export interface LLMServices {
    openAiService: OpenAiService;
    grazieService: GrazieService;
    predefinedProofsService: PredefinedProofsService;
}

export interface ModelsParams {
    openAiParams: OpenAiModelParams[];
    grazieParams: GrazieModelParams[];
    predefinedProofsModelParams: PredefinedProofsModelParams[];
}
