import { LlmPromptInterface } from "./llmPromptInterface";

export interface LLMInterface {
    /**
     * Initializes the message history of the LLM. 
     * This function should be called after the LLM is initialized.
     *  
     * @param llmPrompt The LLM prompt to use to initialize the message history. 
     */
    initHistory(llmPrompt: LlmPromptInterface): void;

    /**
     * Sends a message to the LLM and returns the response. 
     * 
     * @param message The message to send to the LLM.
     * @param choices The number of choices to return. Defaults to 1.
     * @returns A list of choices.
     */
    sendMessageForResponse(message: string, choices: number): Promise<string[]>;

    /**
     * Sends a message to the LLM and returns the response.
     * But garantees that the message history after the call 
     * remains the same as before the call.
     * 
     * @param message The message to send to the LLM.
     * @param choices The number of choices to return. Defaults to 1.
     * @returns A list of choices.
     */
    sendMessageWithoutHistoryChange(message: string, choices: number): Promise<string[]>;
}