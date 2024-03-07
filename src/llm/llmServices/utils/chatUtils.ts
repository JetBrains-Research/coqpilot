import { ChatHistory } from "../chat";

/* `UserAssistantChatItem` and `ItemizedChat` interfaces are used
 * as wrappers for fitting objects with `ChatTokensFitter` &
 * building them into `ChatMessage`-s conveniently
 */

export interface UserAssistantChatItem {
    userMessage: string;
    assistantMessage: string;
}

export type ItemizedChat = UserAssistantChatItem[];

export function itemizedChatToHistory(itemizedChat: ItemizedChat): ChatHistory {
    const chat: ChatHistory = [];
    for (const item of itemizedChat) {
        chat.push({ role: "user", content: item.userMessage });
        chat.push({ role: "assistant", content: item.assistantMessage });
    }
    return chat;
}

export function chatItemToContent(item: UserAssistantChatItem): string[] {
    return [item.userMessage, item.assistantMessage];
}
