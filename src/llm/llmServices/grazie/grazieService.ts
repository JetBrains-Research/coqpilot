import { EventLogger } from "../../../logging/eventLogger";
import { ProofGenerationContext } from "../../proofGenerationContext";
import { GrazieUserModelParams } from "../../userModelParams";
import { ChatHistory, ChatMessage } from "../chat";
import { GeneratedProofImpl, ProofVersion } from "../llmService";
import { LLMServiceImpl } from "../llmService";
import { LLMServiceInternal } from "../llmServiceInternal";
import { GrazieModelParams } from "../modelParams";

import { GrazieApi, GrazieChatRole, GrazieFormattedHistory } from "./grazieApi";
import { GrazieModelParamsResolver } from "./grazieModelParamsResolver";

export class GrazieService extends LLMServiceImpl<
    GrazieUserModelParams,
    GrazieModelParams,
    GrazieService,
    GrazieGeneratedProof,
    GrazieServiceInternal
> {
    protected readonly internal: GrazieServiceInternal;
    protected readonly modelParamsResolver = new GrazieModelParamsResolver();

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

    /**
     * As specified in Grazie REST API, `maxTokensToGenerate` is a constant currently.
     */
    static readonly maxTokensToGeneratePredefined = 1024;
}

export class GrazieGeneratedProof extends GeneratedProofImpl<
    GrazieModelParams,
    GrazieService,
    GrazieGeneratedProof,
    GrazieServiceInternal
> {
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

class GrazieServiceInternal extends LLMServiceInternal<
    GrazieModelParams,
    GrazieService,
    GrazieGeneratedProof,
    GrazieServiceInternal
> {
    readonly api = new GrazieApi(this.debug);

    constructGeneratedProof(
        proof: string,
        proofGenerationContext: ProofGenerationContext,
        modelParams: GrazieModelParams,
        previousProofVersions?: ProofVersion[] | undefined
    ): GrazieGeneratedProof {
        return new GrazieGeneratedProof(
            proof,
            proofGenerationContext,
            modelParams,
            this,
            previousProofVersions
        );
    }

    async generateFromChatImpl(
        chat: ChatHistory,
        params: GrazieModelParams,
        choices: number
    ): Promise<string[]> {
        this.validateChoices(choices);
        let attempts = choices * 2;
        const completions: Promise<string>[] = [];
        const formattedChat = this.formatChatHistory(chat);

        while (completions.length < choices && attempts > 0) {
            completions.push(
                this.api.requestChatCompletion(params, formattedChat)
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
