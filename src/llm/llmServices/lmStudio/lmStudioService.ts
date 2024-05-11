import { EventLogger } from "../../../logging/eventLogger";
import { ProofGenerationContext } from "../../proofGenerationContext";
import { LMStudioUserModelParams } from "../../userModelParams";
import { ChatHistory } from "../chat";
import {
    GeneratedProofImpl,
    LLMService,
    LLMServiceInternal,
    ProofVersion,
} from "../llmService";
import { LMStudioModelParams } from "../modelParams";
import { LMStudioModelParamsResolver } from "../modelParamsResolvers";

export class LMStudioService extends LLMService<
    LMStudioUserModelParams,
    LMStudioModelParams
> {
    protected readonly internal: LMStudioServiceInternal;
    protected readonly modelParamsResolver = new LMStudioModelParamsResolver();

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

export class LMStudioGeneratedProof extends GeneratedProofImpl<LMStudioModelParams> {
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

class LMStudioServiceInternal extends LLMServiceInternal<LMStudioModelParams> {
    constructGeneratedProof(
        proof: string,
        proofGenerationContext: ProofGenerationContext,
        modelParams: LMStudioModelParams,
        previousProofVersions?: ProofVersion[] | undefined
    ): LMStudioGeneratedProof {
        return new LMStudioGeneratedProof(
            proof,
            proofGenerationContext,
            modelParams,
            this,
            previousProofVersions
        );
    }

    async generateFromChatImpl(
        chat: ChatHistory,
        params: LMStudioModelParams,
        choices: number
    ): Promise<string[]> {
        this.validateChoices(choices);
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
            max_tokens: params.maxTokensToGenerate,
        });
    }

    private endpoint(params: LMStudioModelParams): string {
        return `http://localhost:${params.port}/v1/chat/completions`;
    }
}
