import OpenAI from "openai";

import { illegalState } from "../../../utils/throwErrors";
import { ProofGenerationContext } from "../../proofGenerationContext";
import { DeepSeekUserModelParams } from "../../userModelParams";
import { AnalyzedChatHistory, ChatHistory } from "../commonStructures/chat";
import {
    GeneratedRawContent,
    GeneratedRawContentItem,
} from "../commonStructures/generatedRawContent";
import { ProofVersion } from "../commonStructures/proofVersion";
import { GeneratedProofImpl } from "../generatedProof";
import { LLMServiceImpl } from "../llmService";
import { LLMServiceInternal } from "../llmServiceInternal";
import { DeepSeekModelParams } from "../modelParams";
import { toO1CompatibleChatHistory } from "../utils/o1ClassModels";

import { DeepSeekModelParamsResolver } from "./deepSeekModelParamsResolver";

export class DeepSeekService extends LLMServiceImpl<
    DeepSeekUserModelParams,
    DeepSeekModelParams,
    DeepSeekService,
    DeepSeekGeneratedProof,
    DeepSeekServiceInternal
> {
    readonly serviceName = "DeepSeekService";
    protected readonly internal = new DeepSeekServiceInternal(
        this,
        this.eventLogger,
        this.generationsLoggerBuilder
    );
    protected readonly modelParamsResolver = new DeepSeekModelParamsResolver();
}

export class DeepSeekGeneratedProof extends GeneratedProofImpl<
    DeepSeekModelParams,
    DeepSeekService,
    DeepSeekGeneratedProof,
    DeepSeekServiceInternal
> {
    constructor(
        rawProof: GeneratedRawContentItem,
        proofGenerationContext: ProofGenerationContext,
        modelParams: DeepSeekModelParams,
        llmServiceInternal: DeepSeekServiceInternal,
        previousProofVersions?: ProofVersion[]
    ) {
        super(
            rawProof,
            proofGenerationContext,
            modelParams,
            llmServiceInternal,
            previousProofVersions
        );
    }
}

class DeepSeekServiceInternal extends LLMServiceInternal<
    DeepSeekModelParams,
    DeepSeekService,
    DeepSeekGeneratedProof,
    DeepSeekServiceInternal
> {
    static readonly baseApiUrl = "https://api.deepseek.com/v1";

    constructGeneratedProof(
        rawProof: GeneratedRawContentItem,
        proofGenerationContext: ProofGenerationContext,
        modelParams: DeepSeekModelParams,
        previousProofVersions?: ProofVersion[] | undefined
    ): DeepSeekGeneratedProof {
        return new DeepSeekGeneratedProof(
            rawProof,
            proofGenerationContext,
            modelParams,
            this,
            previousProofVersions
        );
    }

    async generateFromChatImpl(
        analyzedChat: AnalyzedChatHistory,
        params: DeepSeekModelParams,
        choices: number
    ): Promise<GeneratedRawContent> {
        LLMServiceInternal.validateChoices(choices);

        const openaiCompatibleApi = new OpenAI({
            apiKey: params.apiKey,
            baseURL: DeepSeekServiceInternal.baseApiUrl,
        });
        const formattedChat = this.formatChatHistory(analyzedChat.chat, params);
        this.logDebug.event("Completion requested", {
            history: formattedChat,
        });

        try {
            const completion =
                await openaiCompatibleApi.chat.completions.create({
                    messages: formattedChat,
                    model: params.modelName,
                    n: choices,
                    temperature: params.temperature,
                    // eslint-disable-next-line @typescript-eslint/naming-convention
                    max_tokens: params.maxTokensToGenerate,
                });
            const rawContentItems = completion.choices.map((choice) => {
                const content = choice.message.content;
                if (content === null) {
                    illegalState("response message content is null");
                }
                return content;
            });

            return this.packContentWithTokensMetrics(
                rawContentItems,
                completion.usage,
                analyzedChat,
                params
            );
        } catch (e) {
            // TODO: Implement error repacking, according to the documentation
            // https://api-docs.deepseek.com/quick_start/error_codes
            // Postponed due to API unavailability
            // throw DeepSeekServiceInternal.repackKnownError(e, params);
            throw e;
        }
    }

    private packContentWithTokensMetrics(
        rawContentItems: string[],
        tokensUsage: OpenAI.Completions.CompletionUsage | undefined,
        analyzedChat: AnalyzedChatHistory,
        params: DeepSeekModelParams
    ): GeneratedRawContent {
        const promptTokens =
            tokensUsage?.prompt_tokens ??
            analyzedChat.estimatedTokens.messagesTokens;
        return LLMServiceInternal.aggregateToGeneratedRawContent(
            rawContentItems,
            promptTokens,
            params.modelName,
            {
                promptTokens: promptTokens,
                generatedTokens: tokensUsage?.completion_tokens,
                tokensSpentInTotal: tokensUsage?.total_tokens,
            }
        );
    }

    private formatChatHistory(
        chat: ChatHistory,
        modelParams: DeepSeekModelParams
    ): ChatHistory {
        return toO1CompatibleChatHistory(
            chat,
            modelParams.modelName,
            "deepseek"
        );
    }
}
