import OpenAI from 'openai';
import { 
    CompletionContext,
    OpenAiModelParams 
} from '../modelParamsInterfaces';
import { LLMServiceInterface } from '../llmServiceInterface';

type GptRole = "function" | "user" | "system" | "assistant";
type History = { role: GptRole; content: string; }[];

export class OpenAiService implements LLMServiceInterface { 
    private createHistory = (completionContext: CompletionContext, systemMessage: string): History => {
        const formattedHistory: History = [];
        for (const theorem of completionContext.sameFileTheorems) {
            formattedHistory.push({ role: 'user', content: theorem.statement });
            formattedHistory.push({ role: 'assistant', content: theorem.proof?.onlyText() ?? "Admitted." });
        }
        formattedHistory.push({ role: 'user', content: completionContext.admitCompletionTarget });

        return [{role: 'system', content: systemMessage}, ...formattedHistory];
    };

    async requestCompletion(
        completionContext: CompletionContext,
        params: OpenAiModelParams
    ): Promise<string[]> {
        // Add retry, add logging
        const openai = new OpenAI({ apiKey: params.apiKey });
        const completion = await openai.chat.completions.create({
            messages: this.createHistory(completionContext, params.prompt),
            model: params.model,
            n: params.choices,
            temperature: params.temperature,
            // eslint-disable-next-line @typescript-eslint/naming-convention
            max_tokens: params.maxTokens, 
        });
        
        return completion.choices.map((choice: any) => choice.message.content);
    }

    dispose(): void {
        return;
    }
}