import {
    ProofGenerationContext,
    GrazieModelParams,
} from "../modelParamsInterfaces";
import { GrazieApiInterface } from "./grazieApiInterface";
import { LLMServiceInterface } from "../llmServiceInterface";
import { GrazieApi, GrazieFormattedHistory } from "./grazieApi";
import { EventLogger } from "../../../logging/eventLogger";
import { pickTheoremsUntilTokenLimit } from "../accumulateTheoremsInContext";

export class GrazieService implements LLMServiceInterface {
    private api: GrazieApiInterface;
    // Is constant (now) as specified in Grazie REST API
    private readonly grazieMaxTokensInCompletion = 1024;

    constructor(eventLogger?: EventLogger) {
        this.api = new GrazieApi(eventLogger);
    }

    private createHistory = (
        proofGenerationContext: ProofGenerationContext,
        params: GrazieModelParams
    ): GrazieFormattedHistory => {
        const theorems = pickTheoremsUntilTokenLimit(
            this.grazieMaxTokensInCompletion,
            proofGenerationContext,
            params.prompt,
            params.model,
            params.modelContextLength
        );
        const formattedHistory: GrazieFormattedHistory = [];
        for (const theorem of theorems) {
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

        return [{ role: "System", text: params.prompt }, ...formattedHistory];
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
            params
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
