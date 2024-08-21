import { EventLogger } from "../../../logging/eventLogger";
import { ProofGenerationContext } from "../../proofGenerationContext";
import { LMStudioUserModelParams } from "../../userModelParams";
import { ChatHistory } from "../chat";
import {
    GeneratedProofImpl,
    LLMServiceImpl,
    ProofVersion,
} from "../llmService";
import { LLMServiceInternal } from "../llmServiceInternal";
import { LMStudioModelParams } from "../modelParams";

import { LMStudioModelParamsResolver } from "./lmStudioModelParamsResolver";

export class LMStudioService extends LLMServiceImpl<
    LMStudioUserModelParams,
    LMStudioModelParams,
    LMStudioService,
    LMStudioGeneratedProof,
    LMStudioServiceInternal
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

export class LMStudioGeneratedProof extends GeneratedProofImpl<
    LMStudioModelParams,
    LMStudioService,
    LMStudioGeneratedProof,
    LMStudioServiceInternal
> {
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

class LMStudioServiceInternal extends LLMServiceInternal<
    LMStudioModelParams,
    LMStudioService,
    LMStudioGeneratedProof,
    LMStudioServiceInternal
> {
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
        analyzedChat: AnalyzedChatHistory,
        params: LMStudioModelParams,
        choices: number
    ): Promise<GeneratedRawContent> {
        LLMServiceInternal.validateChoices(choices);
        let attempts = choices * 2;
        const completions: string[] = [];
        this.debug.logEvent("Completion requested", {
            history: analyzedChat.chat,
        });

        let lastErrorThrown: Error | undefined = undefined;
        while (completions.length < choices && attempts > 0) {
            try {
                const responce = await fetch(this.endpoint(params), {
                    method: "POST",
                    headers: this.headers,
                    body: this.body(analyzedChat.chat, params),
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

        // TODO: find a way to get actual tokens spent instead of approximation
        return LLMServiceInternal.aggregateToGeneratedRawContent(
            completions,
            analyzedChat.estimatedTokens.messagesTokens,
            undefined
        );
    }

    private readonly headers = {
        // eslint-disable-next-line @typescript-eslint/naming-convention
        "Content-Type": "application/json",
    };

    private body(messages: ChatHistory, params: LMStudioModelParams): string {
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
