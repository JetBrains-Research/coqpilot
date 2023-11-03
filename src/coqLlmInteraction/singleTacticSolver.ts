import { LLMInterface } from "./llmInterface";
import { LlmPromptInterface } from "./llmPromptInterface";

export class SingleTacticSolver implements LLMInterface {
    private tactics: string[];

    constructor(tactics: string[]) {
        this.tactics = tactics;
    }

    initHistory(_llmPrompt: LlmPromptInterface): void {
        // Do nothing
    }
    
    async sendMessageWithoutHistoryChange(_message: string, _choices: number): Promise<string[]> {
        return this.tactics.map((tactic) => {
            return `Proof. ${tactic} Qed.`;
        });
    }
}