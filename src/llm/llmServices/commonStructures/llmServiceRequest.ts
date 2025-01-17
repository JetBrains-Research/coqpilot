import { LLMServiceError } from "../../llmServiceErrors";
import { UserModelParams } from "../../userModelParams";
import { LLMService } from "../llmService";
import { ModelParams } from "../modelParams";

import { AnalyzedChatHistory } from "./chat";
import { GeneratedRawContentItem } from "./generatedRawContent";
import { GenerationTokens } from "./generationTokens";
import { ProofGenerationType } from "./proofGenerationType";

/**
 * Interface for `LLMServiceImpl` to package all generation request data.
 * Then, this data is used for interaction between implementation components.
 * In addition, interfaces derived from it can be passed to loggers to record the requests' results.
 */
export interface LLMServiceRequest {
    llmService: LLMService<UserModelParams, ModelParams>;
    proofGenerationType: ProofGenerationType;
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

export function isLLMServiceRequest(data: any): data is LLMServiceRequest {
    const maybeRequest = data as LLMServiceRequest;
    return (
        maybeRequest.llmService !== undefined &&
        maybeRequest.proofGenerationType !== undefined &&
        maybeRequest.params !== undefined &&
        maybeRequest.choices !== undefined
    );
}

export function isLLMServiceRequestSucceeded(
    data: any
): data is LLMServiceRequestSucceeded {
    const maybeSucceedRequest = data as LLMServiceRequestSucceeded;
    return (
        isLLMServiceRequest(data) &&
        maybeSucceedRequest.generatedRawProofs !== undefined &&
        maybeSucceedRequest.tokensSpentInTotal !== undefined
    );
}

export function isLLMServiceRequestFailed(
    data: any
): data is LLMServiceRequestFailed {
    const maybeFailedRequest = data as LLMServiceRequestFailed;
    return (
        isLLMServiceRequest(data) &&
        maybeFailedRequest.llmServiceError !== undefined
    );
}
