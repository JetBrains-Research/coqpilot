import {
    ProofGenerationContext,
    LmStudioModelParams,
} from "../modelParamsInterfaces";
import { LLMServiceInterface } from "../llmServiceInterface";
import { pickTheoremsUntilTokenLimit } from "../pickTheoremsUntilTokenLimit";
import { EventLogger, Severity } from "../../../logging/eventLogger";

type LMStudioChatRole = "user" | "system" | "assistant";
type History = { role: LMStudioChatRole; content: string }[];

export class LmStudioService implements LLMServiceInterface {
    constructor(private readonly eventLogger?: EventLogger) {}

    private readonly headers = {
        // eslint-disable-next-line @typescript-eslint/naming-convention
        "Content-Type": "application/json",
    };

    private body = (messages: History, params: LmStudioModelParams): any =>
        JSON.stringify({
            messages: messages,
            stream: false,
            temperature: params.temperature,
            // eslint-disable-next-line @typescript-eslint/naming-convention
            max_tokens: params.answerMaxTokens,
        });

    private endpoint = (params: LmStudioModelParams): string => {
        return `http://localhost:${params.port}/v1/chat/completions`;
    };

    private createHistory = (
        proofGenerationContext: ProofGenerationContext,
        params: LmStudioModelParams
    ): History => {
        const theorems = pickTheoremsUntilTokenLimit(
            params.answerMaxTokens,
            proofGenerationContext,
            params.prompt,
            "non-openai-model",
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
        params: LmStudioModelParams
    ): Promise<string[]> {
        const formattedHistory = this.createHistory(
            proofGenerationContext,
            params
        );
        this.eventLogger?.log(
            "lm-studio-fetch-started",
            "Completion from LmStudio requested",
            { history: formattedHistory },
            Severity.DEBUG
        );
        const choices = params.choices;
        let attempts = choices * 2;
        const completions: string[] = [];

        while (completions.length < choices && attempts > 0) {
            try {
                const responce = await fetch(this.endpoint(params), {
                    method: "POST",
                    headers: this.headers,
                    body: this.body(formattedHistory, params),
                });
                if (responce.ok) {
                    const res = await responce.json();
                    completions.push(res.choices[0].message.content);
                }
                this.eventLogger?.log(
                    "lm-studio-fetch-success",
                    "Completion from LmStudio succeeded",
                    { completions: completions }
                );
            } catch (err) {
                this.eventLogger?.log(
                    "lm-studio-fetch-failed",
                    "Completion from LmStudio failed",
                    { error: err }
                );
            }
            attempts--;
        }

        return completions;
    }

    dispose(): void {
        return;
    }
}
