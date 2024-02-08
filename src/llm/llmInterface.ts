import { History } from "./types";

export interface LLM {
    /**
     * Responds with a completion to a given message 
     * history, given as a list of pairs of role and
     * content. History is given in the following order:
     * - previous user-system messages
     * - new user message
     * - Does not include the system message.
     * 
     * @param history The message history to respond to.
     * @returns The completion to the message history.
     */ 
    fetchMessage(history: History): Promise<string[]>;

    /**
     * Disposes of the LLM object, freeing resources.
     */
    dispose(): void;
}