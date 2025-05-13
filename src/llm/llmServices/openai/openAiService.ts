import OpenAI from "openai";

import { asErrorOrUndefined } from "../../../utils/errors/errorsUtils";
import { illegalState } from "../../../utils/errors/throwErrors";
import {
    ConfigurationError,
    RemoteConnectionError,
} from "../../llmServiceErrors";
import { ProofGenerationContext } from "../../proofGenerationContext";
import { OpenAiUserModelParams } from "../../userModelParams";
import { AnalyzedChatHistory, ChatHistory } from "../commonStructures/chat";
import {
    GeneratedRawContent,
    GeneratedRawContentItem,
} from "../commonStructures/generatedRawContent";
import { ProofVersion } from "../commonStructures/proofVersion";
import { SchedulersProviderBuilders } from "../commonStructures/schedulersProviders";
import { GeneratedProofImpl } from "../generatedProof";
import { LLMServiceImpl } from "../llmService";
import { LLMServiceIdentifier } from "../llmServiceIdentifier";
import { LLMServiceInternal } from "../llmServiceInternal";
import { OpenAiModelParams } from "../modelParams";
import { toO1CompatibleChatHistory } from "../utils/o1ClassModels";
import { provideBasicSerializer } from "../utils/serialization/basicLLMServiceSerializer";

import { OpenAiModelParamsResolver } from "./openAiModelParamsResolver";

export class OpenAiService extends LLMServiceImpl<
    OpenAiUserModelParams,
    OpenAiModelParams,
    OpenAiService,
    OpenAiGeneratedProof,
    OpenAiServiceInternal
> {
    readonly name = "OpenAiService";
    readonly identifier = LLMServiceIdentifier.OPENAI;

    protected readonly internal = new OpenAiServiceInternal(this);
    protected readonly modelParamsResolver = new OpenAiModelParamsResolver();
    protected readonly serializer = provideBasicSerializer(this);
}

export class OpenAiGeneratedProof extends GeneratedProofImpl<
    OpenAiModelParams,
    OpenAiService,
    OpenAiGeneratedProof,
    OpenAiServiceInternal
> {
    constructor(
        rawProof: GeneratedRawContentItem,
        proofGenerationContext: ProofGenerationContext,
        modelParams: OpenAiModelParams,
        llmServiceInternal: OpenAiServiceInternal,
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

class OpenAiServiceInternal extends LLMServiceInternal<
    OpenAiModelParams,
    OpenAiService,
    OpenAiGeneratedProof,
    OpenAiServiceInternal
> {
    constructGeneratedProof(
        rawProof: GeneratedRawContentItem,
        proofGenerationContext: ProofGenerationContext,
        modelParams: OpenAiModelParams,
        previousProofVersions?: ProofVersion[] | undefined
    ): OpenAiGeneratedProof {
        return new OpenAiGeneratedProof(
            rawProof,
            proofGenerationContext,
            modelParams,
            this,
            previousProofVersions
        );
    }

    readonly modelsSchedulersProvider =
        SchedulersProviderBuilders.limitParallelismForModelsWithSameKey(
            this.serviceSetup.generationParallelism,
            (params: OpenAiModelParams) => params.modelName,
            this.llmService.name,
            this.serviceSetup.enableModelsSchedulingDebugLogs
        );

    async generateFromChatImpl(
        analyzedChat: AnalyzedChatHistory,
        params: OpenAiModelParams,
        choices: number
    ): Promise<GeneratedRawContent> {
        LLMServiceInternal.validateChoices(choices);

        const openai = new OpenAI({ apiKey: params.apiKey });
        const formattedChat = this.formatChatHistory(analyzedChat.chat, params);
        this.logDebug.event("Completion requested", {
            history: formattedChat,
        });

        try {
            const completion = await openai.chat.completions.create({
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
            throw OpenAiServiceInternal.repackKnownError(e, params);
        }
    }

    private packContentWithTokensMetrics(
        rawContentItems: string[],
        tokensUsage: OpenAI.Completions.CompletionUsage | undefined,
        analyzedChat: AnalyzedChatHistory,
        params: OpenAiModelParams
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

    private static repackKnownError(
        caughtObject: any,
        params: OpenAiModelParams
    ): any {
        const error = asErrorOrUndefined(caughtObject);
        if (error === undefined) {
            return caughtObject;
        }
        const errorMessage = error.message;

        if (this.matchesPattern(this.unknownModelNamePattern, errorMessage)) {
            return new ConfigurationError(
                `invalid model name "${params.modelName}", such model does not exist or you do not have access to it`
            );
        }
        if (this.matchesPattern(this.incorrectApiKeyPattern, errorMessage)) {
            return new ConfigurationError(
                `incorrect api key "${params.apiKey}" (check your API key at https://platform.openai.com/account/api-keys)`
            );
        }
        const contextExceeded = this.parsePattern(
            this.maximumContextLengthExceededPattern,
            errorMessage
        );
        if (contextExceeded !== undefined) {
            const [requestedTokens, modelsMaxContextLength] = contextExceeded;
            const intro =
                "`tokensLimit` and `maxTokensToGenerate` are too large together";
            const explanation = `model's maximum context length is ${modelsMaxContextLength} tokens, but was requested ${requestedTokens} tokens`;
            return new ConfigurationError(`${intro}; ${explanation}`);
        }
        if (this.matchesPattern(this.connectionErrorPattern, errorMessage)) {
            return new RemoteConnectionError(
                "failed to reach OpenAI remote service"
            );
        }
        return error;
    }

    private static matchesPattern(pattern: RegExp, text: string): boolean {
        return text.match(pattern) !== null;
    }

    private static parsePattern(
        pattern: RegExp,
        text: string
    ): string[] | undefined {
        const match = text.match(pattern);
        if (!match) {
            return undefined;
        }
        return match.slice(1);
    }

    private static readonly unknownModelNamePattern =
        /^404 The model `(.*)` does not exist or you do not have access to it\.$/;

    private static readonly incorrectApiKeyPattern =
        /^401 Incorrect API key provided: (.*)\.(.*)$/;

    private static readonly maximumContextLengthExceededPattern =
        /^400 max_tokens is too large: ([0-9]+)\. This model supports at most ([0-9]+) completion tokens, whereas you provided ([0-9]+)\..*$/;

    private static readonly connectionErrorPattern = /^Connection error\.$/;

    private formatChatHistory(
        chat: ChatHistory,
        modelParams: OpenAiModelParams
    ): ChatHistory {
        return toO1CompatibleChatHistory(chat, modelParams.modelName, "openai");
    }
}
