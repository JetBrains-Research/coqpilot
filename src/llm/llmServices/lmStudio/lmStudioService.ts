import { EventLogger } from "../../../logging/eventLogger";
import { ConfigurationError } from "../../llmServiceErrors";
import { ProofGenerationContext } from "../../proofGenerationContext";
import { ChatHistory } from "../chat";
import {
    GeneratedProof,
    LLMService,
    LLMServiceInternal,
    ProofVersion,
} from "../llmService";
import { LMStudioModelParams, ModelParams } from "../modelParams";

export class LMStudioService extends LLMService {
    protected readonly internal: LMStudioServiceInternal;

    constructor(
        eventLogger?: EventLogger,
        debugLogs: boolean = false,
        generationsLogsFilePath?: string
    ) {
        super(
            "LMStudioService",
            eventLogger,
            debugLogs,
            generationsLogsFilePath
        );
        this.internal = new LMStudioServiceInternal(
            this,
            this.eventLoggerGetter,
            this.generationsLoggerBuilder
        );
    }
}

export class LMStudioGeneratedProof extends GeneratedProof {
    constructor(
        proof: string,
        proofGenerationContext: ProofGenerationContext,
        modelParams: LMStudioModelParams,
        llmServiceInternal: LMStudioServiceInternal,
        previousProofVersions?: ProofVersion[]
    ) {
        super(
            proof,
            proofGenerationContext,
            modelParams,
            llmServiceInternal,
            previousProofVersions
        );
    }
}

class LMStudioServiceInternal extends LLMServiceInternal {
    constructGeneratedProof(
        proof: string,
        proofGenerationContext: ProofGenerationContext,
        modelParams: ModelParams,
        previousProofVersions?: ProofVersion[] | undefined
    ): GeneratedProof {
        return new LMStudioGeneratedProof(
            proof,
            proofGenerationContext,
            modelParams as LMStudioModelParams,
            this,
            previousProofVersions
        );
    }

    async generateFromChatImpl(
        chat: ChatHistory,
        params: LMStudioModelParams,
        choices: number
    ): Promise<string[]> {
        if (choices <= 0) {
            throw new ConfigurationError(`bad choices: ${choices} <= 0`);
        }
        let attempts = choices * 2;
        const completions: string[] = [];
        this.debug.logEvent("Completion requested", { history: chat });

        let lastErrorThrown: Error | undefined = undefined;
        while (completions.length < choices && attempts > 0) {
            try {
                const responce = await fetch(this.endpoint(params), {
                    method: "POST",
                    headers: this.headers,
                    body: this.body(chat, params),
                });
                if (responce.ok) {
                    const res = await responce.json();
                    const newCompletion = res.choices[0].message.content;
                    completions.push(newCompletion);
                    this.debug.logEvent("Completion succeeded", {
                        newCompletion: newCompletion,
                    });
                }
            } catch (err) {
                this.debug.logEvent("Completion failed", {
                    error: err,
                });
                if ((err as Error) === null) {
                    throw err;
                }
                lastErrorThrown = err as Error;
            }
            attempts--;
        }

        if (completions.length < choices) {
            throw lastErrorThrown;
        }
        return completions;
    }

    private readonly headers = {
        // eslint-disable-next-line @typescript-eslint/naming-convention
        "Content-Type": "application/json",
    };

    private body(messages: ChatHistory, params: LMStudioModelParams): any {
        return JSON.stringify({
            messages: messages,
            stream: false,
            temperature: params.temperature,
            // eslint-disable-next-line @typescript-eslint/naming-convention
            max_tokens: params.newMessageMaxTokens,
        });
    }

    private endpoint(params: LMStudioModelParams): string {
        return `http://localhost:${params.port}/v1/chat/completions`;
    }
}
