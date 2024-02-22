import OpenAI from "openai";
import {
    ProofGenerationContext,
    OpenAiModelParams,
} from "../modelParamsInterfaces";
import { LLMServiceInterface } from "../llmServiceInterface";
import { accumulateTheoremsUntilTokenCount } from "../accumulateTheoremsInContext";

type GptRole = "function" | "user" | "system" | "assistant";
type History = { role: GptRole; content: string }[];

export class OpenAiService implements LLMServiceInterface {
    private createHistory = (
        proofGenerationContext: ProofGenerationContext,
        params: OpenAiModelParams
    ): History => {
        const theorems = accumulateTheoremsUntilTokenCount(
            params.maxTokens,
            proofGenerationContext,
            params.prompt,
            params.model,
            params.modelContextLength
        );
        const formattedHistory: History = [];
        for (const theorem of theorems) {
            formattedHistory.push({ role: "user", content: theorem.statement });
            formattedHistory.push({
                role: "assistant",
                content: theorem.proof?.onlyText() ?? "Admitted.",
            });
        }
        formattedHistory.push({
            role: "user",
            content: proofGenerationContext.admitCompletionTarget,
        });

        return [
            { role: "system", content: params.prompt },
            ...formattedHistory,
        ];
    };

    async generateProof(
        proofGenerationContext: ProofGenerationContext,
        params: OpenAiModelParams
    ): Promise<string[]> {
        // Add retry, add logging
        const openai = new OpenAI({ apiKey: params.apiKey });
        const completion = await openai.chat.completions.create({
            messages: this.createHistory(proofGenerationContext, params),
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
