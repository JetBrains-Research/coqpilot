import { ChatHistory } from "../commonStructures/chat";

/* `UserAssistantChatItem` and `ItemizedChat` interfaces are used
 * as wrappers for fitting objects with `ChatTokensFitter` &
 * building them into `ChatMessage`-s conveniently
 */

export interface UserAssistantChatItem {
    userMessage: string;
    assistantMessage: string;
}

export type ItemizedChat = UserAssistantChatItem[];

export function itemizedChatToHistory(
    itemizedChat: ItemizedChat,
    userFirst: boolean = true
): ChatHistory {
    const chat: ChatHistory = [];
    for (const item of itemizedChat) {
        if (userFirst) {
            chat.push({ role: "user", content: item.userMessage });
            chat.push({ role: "assistant", content: item.assistantMessage });
        } else {
            chat.push({ role: "assistant", content: item.assistantMessage });
            chat.push({ role: "user", content: item.userMessage });
        }
    }
    return chat;
}

export function chatItemToContent(item: UserAssistantChatItem): string[] {
    return [item.userMessage, item.assistantMessage];
}
