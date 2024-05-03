import { EventLogger } from "../../../logging/eventLogger";
import { ProofGenerationContext } from "../../proofGenerationContext";
import { UserModelParams } from "../../userModelParams";
import { ChatHistory, ChatMessage } from "../chat";
import {
    GeneratedProof,
    LLMServiceInternal,
    Proof,
    ProofVersion,
} from "../llmService";
import { LLMService } from "../llmService";
import { GrazieModelParams, ModelParams } from "../modelParams";

import { GrazieApi, GrazieChatRole, GrazieFormattedHistory } from "./grazieApi";

export class GrazieService extends LLMService {
    protected readonly internal: GrazieServiceInternal;

    constructor(
        eventLogger?: EventLogger,
        debug: boolean = false,
        requestsLogsFilePath?: string
    ) {
        super("GrazieService", eventLogger, debug, requestsLogsFilePath);
        this.internal = new GrazieServiceInternal(
            this,
            this.eventLoggerGetter,
            this.requestsLoggerBuilder
        );
    }

    // Is constant (for now) as specified in Grazie REST API
    readonly newMessageMaxTokens = 1024;

    resolveParameters(params: UserModelParams): ModelParams {
        return this.resolveParametersWithDefaults({
            ...params,
            newMessageMaxTokens: this.newMessageMaxTokens,
        });
    }
}

export class GrazieGeneratedProof extends GeneratedProof {
    constructor(
        proof: Proof,
        proofGenerationContext: ProofGenerationContext,
        modelParams: GrazieModelParams,
        llmServiceInternal: GrazieServiceInternal,
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

class GrazieServiceInternal extends LLMServiceInternal {
    readonly api = new GrazieApi(this.eventLogger);

    constructGeneratedProof(
        proof: string,
        proofGenerationContext: ProofGenerationContext,
        modelParams: ModelParams,
        previousProofVersions?: ProofVersion[] | undefined
    ): GeneratedProof {
        return new GrazieGeneratedProof(
            proof,
            proofGenerationContext,
            modelParams as GrazieModelParams,
            this,
            previousProofVersions
        );
    }

    async generateFromChatImpl(
        chat: ChatHistory,
        params: ModelParams,
        choices: number
    ): Promise<string[]> {
        if (choices <= 0) {
            return [];
        }
        let attempts = choices * 2;
        const completions: Promise<string>[] = [];
        const formattedChat = this.formatChatHistory(chat);

        while (completions.length < choices && attempts > 0) {
            completions.push(
                this.api.requestChatCompletion(
                    params as GrazieModelParams,
                    formattedChat
                )
            );
            attempts--;
        }

        return Promise.all(completions);
    }

    private formatChatHistory(chat: ChatHistory): GrazieFormattedHistory {
        return chat.map((message: ChatMessage) => {
            const grazieRoleName =
                message.role[0].toUpperCase() + message.role.slice(1);
            return {
                role: grazieRoleName as GrazieChatRole,
                text: message.content,
            };
        });
    }
}
