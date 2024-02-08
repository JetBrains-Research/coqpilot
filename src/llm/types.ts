export type Role = "user" | "system" | "assistant";

export interface Message {
    role: Role;
    content: string;
}

export type History = Message[];