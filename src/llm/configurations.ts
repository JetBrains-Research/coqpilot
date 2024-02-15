import { 
    OpenAiModelParams,
    GrazieModelParams,
    PredefinedProofsModelParams
} from "./llmService/modelParamsInterfaces";
import { GrazieService } from "./llmService/grazie/grazieService";
import { OpenAiService } from "./llmService/openai/openAiService";
import { 
    PredefinedProofsService 
} from "./llmService/predefinedProofs/predefinedProofsService";

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