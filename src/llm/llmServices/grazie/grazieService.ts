import {
    ProofGenerationContext,
    GrazieModelParams,
} from "../modelParamsInterfaces";
import { GrazieApiInterface } from "./grazieApiInterface";
import { LLMServiceInterface } from "../llmServiceInterface";
import { GrazieApi, GrazieFormattedHistory } from "./grazieApi";

export class GrazieService implements LLMServiceInterface {
    private api: GrazieApiInterface;

    constructor() {
        this.api = new GrazieApi();
    }

    private createHistory = (
        proofGenerationContext: ProofGenerationContext,
        systemMessage: string
    ): GrazieFormattedHistory => {
        const formattedHistory: GrazieFormattedHistory = [];
        for (const theorem of proofGenerationContext.sameFileTheorems) {
            formattedHistory.push({ role: "User", text: theorem.statement });
            formattedHistory.push({
                role: "Assistant",
                text: theorem.proof?.onlyText() ?? "Admitted.",
            });
        }
        formattedHistory.push({
            role: "User",
            text: proofGenerationContext.admitCompletionTarget,
        });

        return [{ role: "System", text: systemMessage }, ...formattedHistory];
    };

    async generateProof(
        proofGenerationContext: ProofGenerationContext,
        params: GrazieModelParams
    ): Promise<string[]> {
        const choices = params.choices;
        let attempts = choices * 2;
        const completions: Promise<string>[] = [];
        const grazieFormattedHistory = this.createHistory(
            proofGenerationContext,
            params.prompt
        );

        while (completions.length < choices && attempts > 0) {
            completions.push(
                this.api.chatCompletionRequest(params, grazieFormattedHistory)
            );
            attempts--;
        }

        return Promise.all(completions);
    }

    dispose(): void {
        return;
    }
}
