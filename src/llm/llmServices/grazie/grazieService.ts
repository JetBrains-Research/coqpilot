import { EventLogger } from "../../../logging/eventLogger";
import { ProofGenerationContext } from "../../proofGenerationContext";
import { UserModelParams } from "../../userModelParams";
import { ChatHistory, ChatMessage } from "../chat";
import {
    GeneratedProof,
    LLMServiceInternal,
    ProofVersion,
} from "../llmService";
import { LLMService } from "../llmService";
import { GrazieModelParams, ModelParams } from "../modelParams";

import { GrazieApi, GrazieChatRole, GrazieFormattedHistory } from "./grazieApi";

export class GrazieService extends LLMService {
    protected readonly internal: GrazieServiceInternal;

    constructor(
        eventLogger?: EventLogger,
        debugLogs: boolean = false,
        generationsLogsFilePath?: string
    ) {
        super("GrazieService", eventLogger, debugLogs, generationsLogsFilePath);
        this.internal = new GrazieServiceInternal(
            this,
            this.eventLoggerGetter,
            this.generationsLoggerBuilder
        );
    }

    // Is constant (for now) as specified in Grazie REST API
    static readonly maxTokensToGeneratePredefined = 1024;

    resolveParameters(params: UserModelParams): ModelParams {
        return this.resolveParametersWithDefaults({
            ...params,
            maxTokensToGenerate: GrazieService.maxTokensToGeneratePredefined,
        });
    }
}

export class GrazieGeneratedProof extends GeneratedProof {
    constructor(
        proof: string,
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
    readonly api = new GrazieApi(this.debug);

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
        this.validateChoices(choices);
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
