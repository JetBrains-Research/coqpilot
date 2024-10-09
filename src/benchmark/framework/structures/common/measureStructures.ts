export interface LengthMetrics {
    inSteps?: number;
    inSymbols?: number;
    inTokens?: number;
}

export interface EstimatedChatTokens {
    requestChatTokens: number;
    responseMessageTokens: number;
    tokensInTotal: number;
}
