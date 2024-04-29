import { EventLogger } from "../../../logging/eventLogger";
import { ProofGenerationContext } from "../../proofGenerationContext";
import { UserModelParams } from "../../userModelParams";
import { ChatHistory, ChatMessage } from "../chat";
import { GeneratedProof, Proof, ProofVersion } from "../llmService";
import { LLMService } from "../llmService";
import { GrazieModelParams, ModelParams } from "../modelParams";

import { GrazieApi, GrazieChatRole, GrazieFormattedHistory } from "./grazieApi";

export class GrazieService extends LLMService {
    private api: GrazieApi;
    // Is constant (now) as specified in Grazie REST API
    private readonly newMessageMaxTokens = 1024;

    constructor(
        requestsLogsFilePath: string,
        eventLogger?: EventLogger,
        debug: boolean = false
    ) {
        super("GrazieService", requestsLogsFilePath, eventLogger, debug);
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
