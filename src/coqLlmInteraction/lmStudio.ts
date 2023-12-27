import { LLMInterface } from "./llmInterface";
import { LlmPromptInterface } from "./llmPromptInterface";
import logger from "../extension/logger";
import { CoqpilotConfigWrapper } from "../extension/config";
import * as utils from "./utils";
import fetch from "node-fetch";

type ChatRole = "user" | "system" | "assistant";

export class LMStudio implements LLMInterface {
    history: { role: ChatRole; content: string; }[];
    readonly config: CoqpilotConfigWrapper;
    
    private readonly headers = {
        // eslint-disable-next-line @typescript-eslint/naming-convention
        "Content-Type": "application/json"
    };

    private body = (messages: { role: ChatRole; content: string; }[]): any => JSON.stringify({
        messages: messages,
        stream: false,
        temperature: 0.7, 
    }); 

    get gateaway(): string {
        return `http://localhost:${this.config.config.lmStudioPort}/v1/chat/completions`;
    }


    constructor(config: CoqpilotConfigWrapper) {
        this.config = config;
        this.history = [];
    }

    initHistory(llmPrompt: LlmPromptInterface): void {
        this.history = [];
        const prompt = llmPrompt.getSystemMessage();
        const messageHistory = llmPrompt.getMessageHistory();

        this.history.push({role: "system", content: prompt});
        const formattedHistory = messageHistory.map((msg) => {
            return {role: msg.role as ChatRole, content: msg.content};
        });

        this.history = this.history.concat(formattedHistory);
    }

    async sendMessageWithoutHistoryChange(message: string, choices: number): Promise<string[]> {
        if (this.config.config.useLmStudio === false) {
            return [];
        } 
        
        const updatedHistory = this.history.concat([{role: "user", content: message}]);
        const completions: string[] = [];
        while (completions.length < choices) {
            try {
                logger.info("Sending request with history: " + JSON.stringify(updatedHistory));
                const completion = await fetch(this.gateaway, {
                    method: "POST",
                    headers: this.headers, 
                    body: this.body(updatedHistory)
                });
                const response = await completion.json();
                const completionText = response.choices[0].message.content;
                if (completionText === undefined) {
                    throw new Error("Completion text is undefined");
                }
                logger.info("Completion text from local LM: " + completionText);
                completions.push(completionText);
            } catch (e : unknown) {
                logger.info("Request to LM studio failed with error '" + utils.toErrorWithMessage(e).message); 
                throw e;
            }
        }

        return completions;
    }
}