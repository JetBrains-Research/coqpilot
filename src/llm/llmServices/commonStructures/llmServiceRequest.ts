import { LLMServiceError } from "../../llmServiceErrors";
import { UserModelParams } from "../../userModelParams";
import { LLMService } from "../llmService";
import { ModelParams } from "../modelParams";

import { AnalyzedChatHistory } from "./chat";
import { GeneratedRawContentItem } from "./generatedRawContent";
import { GenerationTokens } from "./generationTokens";

/**
 * Interface for `LLMServiceImpl` to package all generation request data.
 * Then, this data is used for interaction between implementation components.
 * In addition, interfaces derived from it can be passed to loggers to record the requests' results.
 */
export interface LLMServiceRequest {
    llmService: LLMService<UserModelParams, ModelParams>;
    params: ModelParams;
    choices: number;
    analyzedChat?: AnalyzedChatHistory;
}

export interface LLMServiceRequestSucceeded extends LLMServiceRequest {
    generatedRawProofs: GeneratedRawContentItem[];
    tokensSpentInTotal: GenerationTokens;
}

export interface LLMServiceRequestFailed extends LLMServiceRequest {
    llmServiceError: LLMServiceError;
}
