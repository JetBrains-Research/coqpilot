export type ChatRole = "system" | "user" | "assistant";

export type ChatMessage = { role: ChatRole; content: string };

export type ChatHistory = ChatMessage[];

export interface AnalyzedChatHistory {
    chat: ChatHistory;
    estimatedTokens?: number;
}
