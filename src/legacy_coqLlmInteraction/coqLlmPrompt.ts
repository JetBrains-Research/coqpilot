import { LlmPromptInterface, LlmPromptBase } from "./llmPromptInterface";

export class CoqPromptKShot extends LlmPromptBase implements LlmPromptInterface {
    getSystemMessage(): string {
        return `Generate proof of the theorem from user input in Coq. You should only generate proofs in Coq. Never add special comments to the proof. Your answer should be a valid Coq proof. It should start with 'Proof.' and end with 'Qed.'.`;
    }

    getMessageHistory(): { role: string; content: string; }[] {
        const history: { role: string; content: string; }[] = [];
        for (const theorem of this.trainingTheorems) {
            history.push({role: "user", content: theorem.statement});
            const thrProof = theorem.proof ? theorem.proof.onlyText() : "Admitted.";
            history.push({role: "assistant", content: thrProof});
        }

        return history;
    }
}