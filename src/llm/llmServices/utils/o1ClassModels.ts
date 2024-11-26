import { ChatHistory, ChatMessage } from "../commonStructures/chat";

const o1ClassModels = ['o1-preview', 'o1-preview-2024-09-12', 'o1-mini', 'o1-mini-2024-09-12'];

/**
 * As of November 2024, o1 model requires a different format of chat history.
 * It doesn't support the system prompt, therefore we manually
 * change system prompt to a user's message in case of this specific 
 * model usage.
 */
export function toO1CompatibleChatHistory(
    chatHistory: ChatHistory, 
    modelName: string
): ChatHistory {
    if (o1ClassModels.includes(modelName)) {
        return chatHistory.map((message: ChatMessage) => {
            return {
                role: message.role === "system" ? "user" : message.role,
                content: message.content,
            };
        });
    } else {
        return chatHistory;
    }
}