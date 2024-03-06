import { GrazieModelParams, ModelParams } from "../modelParams";
import {
    GeneratedProof,
    Proof,
    ProofGenerationContext,
    ProofVersion,
} from "../llmService";
import { GrazieApiInterface } from "./grazieApiInterface";
import { LLMService } from "../llmService";
import { GrazieApi, GrazieChatRole, GrazieFormattedHistory } from "./grazieApi";
import { EventLogger } from "../../../logging/eventLogger";
import { ChatHistory, ChatMessage } from "../chat";
import { UserModelParams } from "../userModelParams";

export class GrazieService extends LLMService {
    private api: GrazieApiInterface;
    // Is constant (now) as specified in Grazie REST API
    private readonly newMessageMaxTokens = 1024;

    constructor(eventLogger?: EventLogger) {
        super(eventLogger);
        this.api = new GrazieApi(eventLogger);
    }

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

    async generateFromChat(
        chat: ChatHistory,
        params: ModelParams,
        choices: number
    ): Promise<string[]> {
        let attempts = choices * 2;
        const completions: Promise<string>[] = [];
        const formattedChat = this.formatChatHistory(chat);

        while (completions.length < choices && attempts > 0) {
            completions.push(
                this.api.chatCompletionRequest(
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

    resolveParameters(params: UserModelParams): ModelParams {
        params.newMessageMaxTokens = this.newMessageMaxTokens;
        return this.resolveParametersWithDefaults(params);
    }
}

export class GrazieGeneratedProof extends GeneratedProof {
    constructor(
        proof: Proof,
        proofGenerationContext: ProofGenerationContext,
        modelParams: GrazieModelParams,
        llmService: GrazieService,
        previousProofVersions?: ProofVersion[]
    ) {
        super(
            proof,
            proofGenerationContext,
            modelParams,
            llmService,
            previousProofVersions
        );
    }
}
