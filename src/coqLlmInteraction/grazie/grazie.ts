import { LLMInterface } from "../llmInterface";
import { GrazieApi } from "./grazieApi";
import logger from "../../extension/logger";
import { CoqpilotConfigWrapper } from "../../extension/config";
import * as utils from "../utils";
import { 
    grazieRoleFromString, 
    ChatInstance, 
    Message, 
    Profile,
    appendToHistory, 
    ChatRole
} from "./chatInstance";
import { LlmPromptInterface } from "../llmPromptInterface";

export class Grazie implements LLMInterface {
    private readonly config: CoqpilotConfigWrapper;
    private readonly requestAttempts: number;
    private readonly api: GrazieApi;
    private history: ChatInstance | undefined = undefined;

    constructor(config: CoqpilotConfigWrapper, requestAttempts: number = 3) {
        this.config = config;
        this.requestAttempts = requestAttempts;
        this.api = new GrazieApi();
    }

    initHistory(llmPrompt: LlmPromptInterface): void {
        const prompt = llmPrompt.getSystemMessage();
        const messageHistory = llmPrompt.getMessageHistory();

        const history: Message[] = messageHistory.map((msg) => {
            return {role: grazieRoleFromString(msg.role), text: msg.content};
        });

        this.history = {
            systemMessage: prompt,
            messages: history,
        };
    }

    async sendMessageWithoutHistoryChange(message: string, choices: number): Promise<string[]> {
        if (this.config.config.grazieModel === Profile.NONE) {
            // In general, I want settings to have effect immediately 
            // after change. Mostly, it works well. However, it is
            // not obvious how to remove eg grazie llm interface
            // instance from the iterator, if the iterator is constructed in 
            // the very beginning. To solve this issue, when user turns off 
            // Grazie completion DURING the work of the plugin, I return 
            // an empty completion array result for it. It must not  
            // affect the correctness.
            return [];
        }

        let attempts = this.requestAttempts;
        logger.info("Start sending message to grazie-ai");
        const completions: string[] = [];
        while (completions.length < choices) {
            if (this.history === undefined) {
                throw new Error("History is undefined. Please report this error.");
            }
            logger.info("Sending request with history: " + JSON.stringify(this.history));
            
            await this.api.chatCompletionRequest(
                appendToHistory(this.history, {role: ChatRole.User, text: message}),
                this.config.config.grazieModel as Profile, 
                this.config.config.grazieApiKey
            ).then((response) => {
                completions.push(response);
                logger.info("Request to grazie succeeded");
            }).catch((error) => {
                attempts -= 1;
                if (attempts === 0) {
                    throw error;
                } else {
                    logger.info("Request to grazie failed with error '" + utils.toErrorWithMessage(error).message + "' Retrying..."); 
                }
            });
        }

        return completions;
    }
}