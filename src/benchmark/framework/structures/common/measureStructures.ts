export interface LengthMetrics {
    inSymbols?: number;
    inStepsEstimated?: number;
}

export interface EstimatedChatTokens {
    requestChatTokens: number;
    responseMessageTokens: number;
    tokensInTotal: number;
}
