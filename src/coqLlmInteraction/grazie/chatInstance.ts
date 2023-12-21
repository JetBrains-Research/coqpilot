/* eslint-disable @typescript-eslint/naming-convention */
export enum ChatRole {
    User = "User",
    System = "System",
    Assistant = "Assistant",
}

export function grazieRoleFromString(chatRole: string): ChatRole {
    switch (chatRole) {
        case "user": return ChatRole.User;
        case "system": return ChatRole.System;
        case "assistant": return ChatRole.Assistant;
        default: throw new Error("Invalid chat role: " + chatRole);
    }
}

export enum Profile {
    NONE = "None",
    GPT4 = "openai-gpt-4",
    GPT35 = "openai-chat-gpt",
    LLAMA7B = "grazie-chat-llama-v2-7b", 
    LLAMA13B = "grazie-chat-llama-v2-13b",
    ZEPHYR7B = "grazie-chat-zephyr-7b",
    QWENTURBO = "qwen-turbo", 
    QWENPLUS = "qwen-plus"
}

export interface Message {
    role: ChatRole;
    text: string;
}

export interface ChatInstance {
    systemMessage: string;
    messages: Message[];
}

export function appendToHistory(chat: ChatInstance, message: Message): ChatInstance {
    const newHistory = chat.messages.concat([message]);
    return {
        systemMessage: chat.systemMessage,
        messages: newHistory,
    };
}

export function toJson(chat: ChatInstance, llmProfile: Profile): string {
    const systemMessage = {
        role: ChatRole.System.toString(),
        text: chat.systemMessage,
    }; 
    
    const history = chat.messages.map((message) => {
        return {
            role: message.role.toString(),
            text: message.text,
        };
    });

    const chatComplete = [systemMessage, ...history];
    const chatJson = {
        messages: chatComplete,
    };

    const body = {
        chat: chatJson,
        profile: llmProfile.toString(),
    };

    return JSON.stringify(body);
}