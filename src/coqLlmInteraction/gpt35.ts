import { LLMInterface } from "./llmInterface";
import { LLMPrompt } from "./llmPromptInterface";
import OpenAI from 'openai';

type GptRole = "function" | "user" | "system" | "assistant";

export class GPT35 implements LLMInterface {
    history: { role: GptRole; content: string; }[];
    readonly apiKey: string;
    readonly requestAttempts: number;
    readonly model: string;
    openai: OpenAI;

    constructor(apiKey: string, requestAttempts: number = 3, model: string = "gpt-3.5-turbo-0301") {
        this.apiKey = apiKey;
        this.requestAttempts = requestAttempts;
        this.model = model;
        this.history = [];
        this.openai = new OpenAI({ apiKey: this.apiKey });
    }

    initHistory(llmPrompt: LLMPrompt): void {
        this.history = [];
        const prompt = llmPrompt.getSystemMessage();
        const messageHistory = llmPrompt.getMessageHistory();

        this.history.push({role: "system", content: prompt});
        const gptFormattedHistory = messageHistory.map((msg) => {
            return {role: msg.role as GptRole, content: msg.content};
        });

        this.history = this.history.concat(gptFormattedHistory);
    }

    async sendMessageWithoutHistoryChange(message: string, choices: number): Promise<string[]> {
        let attempts = this.requestAttempts;
        let completion = null;
        console.log("Start sending message to open-ai");
        while (attempts > 0) {
            try {
                console.log("Sending request with history: " + JSON.stringify(this.history.concat([{role: "user", content: message}])));
                completion = await this.openai.chat.completions.create({
                    messages: this.history.concat([{role: "user", content: message}]),
                    model: this.model,
                    n: choices
                });
                console.log("Request to open-ai succeeded");
                return completion.choices.map((choice) => choice.message.content);
            } catch (e) {
                attempts -= 1;
                if (attempts === 0) {
                    throw e;
                } else {
                    console.log("Request to open-ai failed with error " + e + "Retrying..."); 
                    continue;
                }
            }
        }

        throw new Error("Unreachable code reached");
    }
}