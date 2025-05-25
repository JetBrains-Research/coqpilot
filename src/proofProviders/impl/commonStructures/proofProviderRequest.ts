import { ProofProviderError } from "../../proofProviderErrors";
import { ModelParams } from "../modelParams";
import { ProofProvider } from "../proofProvider";

import { AnalyzedChatHistory } from "./chat";
import { GeneratedRawContentItem } from "./generatedRawContent";
import { GenerationTokens } from "./generationTokens";
import { ProofGenerationType } from "./proofGenerationType";

/**
 * Interface for `ProofProvider` to package all generation request data.
 * Then, this data is used for interaction between implementation components.
 * In addition, interfaces derived from it can be passed to loggers to record the requests' results.
 */
export interface ProofProviderRequest {
    proofProvider: ProofProvider;
    proofGenerationType: ProofGenerationType;
    params: ModelParams;
    choices: number;
    analyzedChat?: AnalyzedChatHistory;
}

export interface ProofProviderRequestSucceeded extends ProofProviderRequest {
    generatedRawProofs: GeneratedRawContentItem[];
    tokensSpentInTotal: GenerationTokens;
}

export interface ProofProviderRequestFailed extends ProofProviderRequest {
    proofProviderError: ProofProviderError;
}

export function isProofProviderRequest(
    data: any
): data is ProofProviderRequest {
    const maybeRequest = data as ProofProviderRequest;
    return (
        maybeRequest.proofProvider !== undefined &&
        maybeRequest.proofGenerationType !== undefined &&
        maybeRequest.params !== undefined &&
        maybeRequest.choices !== undefined
    );
}

export function isProofProviderRequestSucceeded(
    data: any
): data is ProofProviderRequestSucceeded {
    const maybeSucceedRequest = data as ProofProviderRequestSucceeded;
    return (
        isProofProviderRequest(data) &&
        maybeSucceedRequest.generatedRawProofs !== undefined &&
        maybeSucceedRequest.tokensSpentInTotal !== undefined
    );
}

export function isProofProviderRequestFailed(
    data: any
): data is ProofProviderRequestFailed {
    const maybeFailedRequest = data as ProofProviderRequestFailed;
    return (
        isProofProviderRequest(data) &&
        maybeFailedRequest.proofProviderError !== undefined
    );
}
