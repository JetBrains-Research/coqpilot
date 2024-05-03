import { EventLogger, Severity } from "../../../logging/eventLogger";
import { ProofGenerationContext } from "../../proofGenerationContext";
import { ChatHistory } from "../chat";
import {
    GeneratedProof,
    LLMService,
    LLMServiceInternal,
    Proof,
    ProofVersion,
} from "../llmService";
import { LMStudioModelParams, ModelParams } from "../modelParams";

export class LMStudioService extends LLMService {
    protected readonly internal: LMStudioServiceInternal;

    constructor(
        eventLogger?: EventLogger,
        debug: boolean = false,
        requestsLogsFilePath?: string
    ) {
        super("LMStudioService", eventLogger, debug, requestsLogsFilePath);
        this.internal = new LMStudioServiceInternal(
            this,
            this.eventLoggerGetter,
            this.requestsLoggerBuilder
        );
    }
}

export class LMStudioGeneratedProof extends GeneratedProof {
    constructor(
        proof: Proof,
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
        this.eventLogger?.log(
            "lm-studio-fetch-started",
            "Completion from LmStudio requested",
            { history: chat },
            Severity.DEBUG
        );
        let attempts = choices * 2;
        const completions: string[] = [];

        while (completions.length < choices && attempts > 0) {
            try {
                const responce = await fetch(this.endpoint(params), {
                    method: "POST",
                    headers: this.headers,
                    body: this.body(chat, params),
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
                // TODO: rethrow error?
            }
            attempts--;
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
