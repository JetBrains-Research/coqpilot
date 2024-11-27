import { ChatHistory, ChatMessage } from "../commonStructures/chat";

const o1ClassModelsOpenAI = [
    "o1-preview",
    "o1-preview-2024-09-12",
    "o1-mini",
    "o1-mini-2024-09-12",
];
const o1ClassModelsGrazie = ["openai-o1", "openai-o1-mini"];

/**
 * As of November 2024, o1 model requires a different format of chat history.
 * It doesn't support the system prompt, therefore we manually
 * change system prompt to a user's message in case of this specific
 * model usage.
 */
export function toO1CompatibleChatHistory(
    chatHistory: ChatHistory,
    modelName: string,
    service: "openai" | "grazie"
): ChatHistory {
    const o1ClassModels =
        service === "openai" ? o1ClassModelsOpenAI : o1ClassModelsGrazie;
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