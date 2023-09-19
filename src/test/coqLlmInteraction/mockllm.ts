import { LLMInterface } from "../../coqLlmInteraction/llmInterface";
import { LlmPromptInterface } from "../../coqLlmInteraction/llmPromptInterface";
import * as assert from 'assert';

export class MockLlmPrompt implements LLMInterface {
    answers: { [key: string]: string[] };

    constructor() {
        this.answers = {};
        this.answers["Theorem test: True."] = ["Proof. Qed.", "Proof. trivial. Qed."];
        this.answers["Theorem test2: False."] = ["Proof. trivial. Qed.", "Proof. trivial. Qed."];
        this.answers["Theorem test3: 1 = 1."] = ["Proof. reflexivity. Qed.", "Proof. trivial. Qed."];
    }

    initHistory(llmPrompt: LlmPromptInterface): void {
        assert(llmPrompt);
    }
    async sendMessageForResponse(message: string, choices: number): Promise<string[]> {
        if(choices > this.answers[message].length) {
            return Array(choices).fill(this.answers[message][0]);
        }
        return this.answers[message];
    }
    async sendMessageWithoutHistoryChange(message: string, choices: number): Promise<string[]> {
        if(choices > this.answers[message].length) {
            return Array(choices).fill(this.answers[message][0]);
        }
        return this.answers[message];
    }
}