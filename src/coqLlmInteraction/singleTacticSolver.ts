import { LLMInterface } from "./llmInterface";
import { LlmPromptInterface } from "./llmPromptInterface";
import { CoqpilotConfigWrapper } from "../extension/config";

export class SingleTacticSolver implements LLMInterface {
    private configWrapped: CoqpilotConfigWrapper; 

    constructor(configWrapped: CoqpilotConfigWrapper) {
        this.configWrapped = configWrapped;
    }

    initHistory(_llmPrompt: LlmPromptInterface): void {
        // Do nothing
    }
    
    async sendMessageWithoutHistoryChange(_message: string, _choices: number): Promise<string[]> {
        return this.configWrapped.config.extraCommandsList.map((tactic) => {
            return `Proof. ${tactic} Qed.`;
        });
    }
}