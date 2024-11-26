import { EventLogger } from "../../../logging/eventLogger";
import { ProofGenerationContext } from "../../proofGenerationContext";
import { GrazieUserModelParams } from "../../userModelParams";
import {
    AnalyzedChatHistory,
    ChatHistory,
    ChatMessage,
} from "../commonStructures/chat";
import { GeneratedRawContent } from "../commonStructures/generatedRawContent";
import { ProofVersion } from "../commonStructures/proofVersion";
import { GeneratedProofImpl } from "../generatedProof";
import { LLMServiceImpl } from "../llmService";
import { LLMServiceInternal } from "../llmServiceInternal";
import { GrazieModelParams } from "../modelParams";
import { toO1CompatibleChatHistory } from "../utils/o1ClassModels";

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
        analyzedChat: AnalyzedChatHistory,
        params: GrazieModelParams,
        choices: number
    ): Promise<GeneratedRawContent> {
        LLMServiceInternal.validateChoices(choices);
        const completions: Promise<string>[] = [];
        const formattedChat = this.formatChatHistory(analyzedChat.chat, params);

        while (completions.length <= choices) {
            completions.push(
                this.api.requestChatCompletion(params, formattedChat)
            );
        }
        const rawContentItems = await Promise.all(completions);

        // TODO: find a way to get actual tokens spent instead of approximation
        return LLMServiceInternal.aggregateToGeneratedRawContent(
            rawContentItems,
            analyzedChat.estimatedTokens.messagesTokens,
            params.modelName
        );
    }

    private formatChatHistory(
        chat: ChatHistory,
        modelParams: GrazieModelParams
    ): GrazieFormattedHistory {
        const o1CompatibleChatHistory = toO1CompatibleChatHistory(chat, modelParams.modelName);

        return o1CompatibleChatHistory.map((message: ChatMessage) => {
            const grazieRoleName =
                message.role[0].toUpperCase() + message.role.slice(1);
            return {
                role: grazieRoleName as GrazieChatRole,
                text: message.content,
            };
        });
    }
}
