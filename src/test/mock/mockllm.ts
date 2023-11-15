import { LLMInterface } from "../../coqLlmInteraction/llmInterface";
import { LlmPromptInterface } from "../../coqLlmInteraction/llmPromptInterface";
import * as assert from 'assert';
import * as common from '../common';

export class MockLlmPrompt implements LLMInterface {
    answers: { [key: string]: string[] };
    delay: number;

    constructor(delay: number = 0) {
        this.answers = {};
        this.answers["Theorem test: True."] = ["Proof. Qed.", "Proof. trivial. Qed."];
        this.answers["Theorem test2: False."] = ["Proof. trivial. Qed.", "Proof. trivial. Qed."];
        this.answers["Theorem test3: 1 = 1."] = ["Proof. reflexivity. Qed.", "Proof. trivial. Qed."];
        this.delay = delay;
    }

    initHistory(llmPrompt: LlmPromptInterface): void {
        assert(llmPrompt);
    }
    
    async sendMessageWithoutHistoryChange(message: string, choices: number): Promise<string[]> {
        await common.sleep(this.delay);
        if (this.answers[message] === undefined) { 
            return Array(choices).fill("Proof.\nauto.\nQed.");
        }
        if(choices !== this.answers[message].length) {
            return Array(choices).fill(this.answers[message][0]);
        }
        return this.answers[message];
    }
}