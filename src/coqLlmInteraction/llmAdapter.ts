import { LLMInterface } from "./llmInterface";
import { LlmPromptInterface } from "./llmPromptInterface";

export class LLMAdapter implements LLMInterface {
    private subscribedModels: LLMInterface[];

    constructor(models: LLMInterface[]) {
        this.subscribedModels = models;
    }

    initHistory(llmPrompt: LlmPromptInterface): void {
        this.subscribedModels.forEach(model => model.initHistory(llmPrompt));
    }
    
    async sendMessageWithoutHistoryChange(message: string, choices: number): Promise<string[]> {
        let promises = this.subscribedModels.map(model => model.sendMessageWithoutHistoryChange(message, choices));
        const results = await Promise.all(promises);
        let responses: string[] = [];

        results.forEach((result) => {
            responses = responses.concat(result);
        });
        
        return responses;
    }
}