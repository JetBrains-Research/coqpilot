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
import { asErrorOrRethrow } from "../../../utils/errorsUtils";

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

        let attempts = choices * 2;
        const completions: string[] = [];
        const tokenMetrics: TokenMetrics[] = [];

        let lastErrorThrown: Error | undefined = undefined;
        while (completions.length < choices && attempts > 0) {
            try {
                const completion =
                    await openaiCompatibleApi.chat.completions.create({
                        messages: formattedChat,
                        model: params.modelName,
                        // At the moment, DeepSeek API supports only n = 1
                        n: 1,
                        temperature: params.temperature,
                        // eslint-disable-next-line @typescript-eslint/naming-convention
                        max_tokens: params.maxTokensToGenerate,
                    });

                tokenMetrics.push(completion.usage);
                if (completion.choices.length !== 1) {
                    illegalState(
                        `expected exactly one completion, got ${completion.choices.length}`
                    );
                }
                const content = completion.choices[0].message.content;
                completion.usage
                if (content === null) {
                    illegalState("response message content is null");
                }

                completions.push(content);
            } catch (err) {
                this.logDebug.event("Completion failed", {
                    error: err,
                });
                lastErrorThrown = asErrorOrRethrow(err);
            }
            attempts--;
        }

        if (completions.length < choices) {
            // TODO: Implement error repacking, according to the documentation
            // https://api-docs.deepseek.com/quick_start/error_codes
            // Postponed due to API unavailability
            // throw DeepSeekServiceInternal.repackKnownError(e, params);

            // UPD: Maybe it won't be needed, API produces well-structured errors
            // and they are shown to the user in a readable format
            throw lastErrorThrown;
        }

        return this.packContentWithTokensMetrics(
            completions,
            this.accumulateTokenMetrics(tokenMetrics),
            analyzedChat,
            params
        );
    }

    private accumulateTokenMetrics(
        tokenUsages: TokenMetrics[]
    ): TokenMetrics {
        const availableTokenUsages = tokenUsages.filter(
            (usage): usage is OpenAI.Completions.CompletionUsage =>
                usage !== undefined
        );

        if (availableTokenUsages.length === 0) {
            return undefined;
        }

        return availableTokenUsages.reduce(
            (acc, usage) => {
                return {
                    completion_tokens: acc.completion_tokens + usage.completion_tokens,
                    prompt_tokens: acc.prompt_tokens + usage.prompt_tokens,
                    total_tokens: acc.total_tokens + usage.total_tokens,
                };
            },
            {
                completion_tokens: 0,
                prompt_tokens: 0,
                total_tokens: 0,
            }
        );
    }

    private packContentWithTokensMetrics(
        rawContentItems: string[],
        tokensUsage: TokenMetrics,
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

type TokenMetrics = OpenAI.Completions.CompletionUsage | undefined;