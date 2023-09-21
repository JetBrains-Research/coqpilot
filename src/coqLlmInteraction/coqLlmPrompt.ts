import { LlmPromptInterface } from "./llmPromptInterface";
import { ProofView, coqlspmodels, ProgressBar, CliProgressBar } from "coqlsp-client";

export class CoqPromptKShot extends LlmPromptInterface {
    static override async init(
        pathToCoqFile: string, 
        pathToRootDir: string,
        tokenLimit: number,
        proofView: ProofView | undefined = undefined,
        progressBar: ProgressBar | undefined = new CliProgressBar(),
        theoremsFromFile: coqlspmodels.Theorem[] | undefined = undefined,
    ): Promise<CoqPromptKShot> {
        const proofViewToUse = proofView ? proofView : await ProofView.init(pathToCoqFile, pathToRootDir, progressBar);

        const llmPrompt = new CoqPromptKShot(
            pathToCoqFile,
            pathToRootDir,
            proofViewToUse,
            progressBar
        );

        return await super.initFromChild(llmPrompt, tokenLimit, theoremsFromFile);
    }

    override getSystemMessage(): string {
        return `Generate proof of the theorem from user input in Coq. You should only generate proofs in Coq. Never add special comments to the proof. Your answer should be a valid Coq proof. It should start with 'Proof.' and end with 'Qed.'.`;
    }

    override getMessageHistory(): { role: string; content: string; }[] {
        const history = [];
        for (const theorem of this.trainingTheorems) {
            history.push({role: "user", content: theorem.statement});
            const thrProof = theorem.proof ? theorem.proof.onlyText() : "Admitted.";
            history.push({role: "assistant", content: thrProof});
        }

        return history;
    }
}