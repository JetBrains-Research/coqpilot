export type ChatRole = "system" | "user" | "assistant";

export type ChatMessage = { role: ChatRole; content: string };

export type ChatHistory = ChatMessage[];

export interface AnalyzedChatHistory {
    chat: ChatHistory;
    estimatedTokens?: EstimatedTokens;
}

export interface EstimatedTokens {
    messagesTokens: number;
    maxTokensToGenerate: number;
    maxTokensInTotal: number;
}
