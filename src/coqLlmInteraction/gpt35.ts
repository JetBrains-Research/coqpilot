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

    private acceptMessage(message: string) {
        this.history.push({role: "user", content: message});
    }

    private async getNextResponses(choices: number = 1): Promise<string[]> {
        const completion = await this.openai.chat.completions.create({
            messages: this.history,
            model: this.model,
            n: choices
        });

        const bestResponse = completion.choices[0].message.content;
        this.history.push({role: "assistant", content: bestResponse});

        return completion.choices.map((choice) => choice.message.content);
    }

    initHistory(llmPrompt: LLMPrompt): void {
        const prompt = llmPrompt.getSystemMessage();
        const messageHistory = llmPrompt.getMessageHistory();

        this.history.push({role: "system", content: prompt});
        const gptFormattedHistory = messageHistory.map((msg) => {
            return {role: msg.role as GptRole, content: msg.content};
        });

        this.history = this.history.concat(gptFormattedHistory);
    }

    async sendMessageForResponse(message: string, choices: number): Promise<string[]> {
        this.acceptMessage(message);
        return this.getNextResponses(choices);
    }

    async sendMessageWithoutHistoryChange(message: string, choices: number): Promise<string[]> {
        let attempts = this.requestAttempts;
        while (attempts > 0) {
            try {
                const completion = await this.openai.chat.completions.create({
                    messages: this.history.concat([{role: "user", content: message}]),
                    model: this.model,
                    n: choices
                });

                return completion.choices.map((choice) => choice.message.content);
            } catch (e) {
                attempts -= 1;
                if (attempts === 0) {
                    throw e;
                } else {
                    continue;
                }
            }
        }

        throw new Error("Unreachable code reached. Report an issue.");
    }
}