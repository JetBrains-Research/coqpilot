import { 
    CompletionContext,
    GrazieModelParams,
} from '../modelParamsInterfaces';
import { GrazieApiInterface } from './grazieApiInterface';
import { LLMServiceInterface } from '../llmServiceInterface';
import { GrazieFormattedHistory } from './grazieApi';

export class GrazieService implements LLMServiceInterface {
    private api: GrazieApiInterface; 

    constructor(api: GrazieApiInterface) {
        this.api = api;
    }

    private createHistory = (completionContext: CompletionContext, systemMessage: string): GrazieFormattedHistory => {
        const formattedHistory: GrazieFormattedHistory = [];
        for (const theorem of completionContext.sameFileTheorems) {
            formattedHistory.push({ role: 'User', text: theorem.statement });
            formattedHistory.push({ role: 'Assistant', text: theorem.proof?.onlyText() ?? "Admitted." });
        }
        formattedHistory.push({ role: 'User', text: completionContext.admitCompletionTarget });

        return [{role: 'System', text: systemMessage}, ...formattedHistory];
    };

    async requestCompletion(
        completionContext: CompletionContext, 
        params: GrazieModelParams
    ): Promise<string[]> {
        const choices = params.choices;
        let attempts = choices * 2;
        const completions: Promise<string>[] = [];
        const grazieFormattedHistory = this.createHistory(completionContext, params.prompt);

        while (completions.length < choices && attempts > 0) {
            completions.push(this.api.chatCompletionRequest(params, grazieFormattedHistory));
            attempts--;
        }

        return Promise.all(completions);
    }

    dispose(): void {
        return;
    }
}