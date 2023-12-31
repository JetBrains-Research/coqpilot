import { LLMInterface } from "./llmInterface";
import { LlmPromptInterface } from "./llmPromptInterface";
import OpenAI from 'openai';
import logger from "../extension/logger";
import { CoqpilotConfigWrapper } from "../extension/config";
import * as utils from "./utils";

type GptRole = "function" | "user" | "system" | "assistant";

export class GPT35 implements LLMInterface {
    history: { role: GptRole; content: string; }[];
    readonly requestAttempts: number;
    readonly config: CoqpilotConfigWrapper;
    openai: OpenAI;
    apiKey: string;

    constructor(config: CoqpilotConfigWrapper, requestAttempts: number = 3) {
        this.config = config;
        this.requestAttempts = requestAttempts;
        this.history = [];
        this.apiKey = config.config.openaiApiKey;
        this.openai = new OpenAI({ apiKey: this.apiKey });
    }

    private updateOpenAi() {
        if (this.config.config.openaiApiKey !== this.apiKey) {
            this.apiKey = this.config.config.openaiApiKey;
            this.openai = new OpenAI({ apiKey: this.apiKey });
        }
    }

    initHistory(llmPrompt: LlmPromptInterface): void {
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
        if (this.config.config.gptModel === "None") {
            throw new Error("GPT model is not set");
        } 
        
        this.updateOpenAi();
        let attempts = this.requestAttempts;
        let completion: any = null;
        logger.info("Start sending message to open-ai");
        while (attempts > 0) {
            try {
                logger.info("Sending request with history: " + JSON.stringify(this.history.concat([{role: "user", content: message}])));
                completion = await this.openai.chat.completions.create({
                    messages: this.history.concat([{role: "user", content: message}]),
                    model: this.config.config.gptModel,
                    n: choices
                });
                logger.info("Request to open-ai succeeded");
                return completion.choices.map((choice: any) => choice.message.content);
            } catch (e : unknown) {
                attempts -= 1;
                if (attempts === 0) {
                    throw e;
                } else {
                    logger.info("Request to open-ai failed with error '" + utils.toErrorWithMessage(e).message + "' Retrying..."); 
                    continue;
                }
            }
        }

        throw new Error("Unreachable code reached");
    }
}