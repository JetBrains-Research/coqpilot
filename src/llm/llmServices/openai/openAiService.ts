import OpenAI from "openai";

import { EventLogger } from "../../../logging/eventLogger";
import { ConfigurationError } from "../../llmServiceErrors";
import { ProofGenerationContext } from "../../proofGenerationContext";
import { OpenAiUserModelParams } from "../../userModelParams";
import { ChatHistory } from "../chat";
import {
    GeneratedProofImpl,
    LLMServiceImpl,
    LLMServiceInternal,
    ProofVersion,
} from "../llmService";
import { OpenAiModelParams } from "../modelParams";

import { OpenAiModelParamsResolver } from "./openAiModelParamsResolver";

export class OpenAiService extends LLMServiceImpl<
    OpenAiUserModelParams,
    OpenAiModelParams,
    OpenAiService,
    OpenAiGeneratedProof,
    OpenAiServiceInternal
> {
    protected readonly internal: OpenAiServiceInternal;
    protected readonly modelParamsResolver = new OpenAiModelParamsResolver();

    constructor(
        eventLogger?: EventLogger,
        debugLogs: boolean = false,
        generationsLogsFilePath?: string
    ) {
        super("OpenAiService", eventLogger, debugLogs, generationsLogsFilePath);
        this.internal = new OpenAiServiceInternal(
            this,
            this.eventLoggerGetter,
            this.generationsLoggerBuilder
        );
    }
}

export class OpenAiGeneratedProof extends GeneratedProofImpl<
    OpenAiModelParams,
    OpenAiService,
    OpenAiGeneratedProof,
    OpenAiServiceInternal
> {
    constructor(
        proof: string,
        proofGenerationContext: ProofGenerationContext,
        modelParams: OpenAiModelParams,
        llmServiceInternal: OpenAiServiceInternal,
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

class OpenAiServiceInternal extends LLMServiceInternal<
    OpenAiModelParams,
    OpenAiService,
    OpenAiGeneratedProof,
    OpenAiServiceInternal
> {
    constructGeneratedProof(
        proof: string,
        proofGenerationContext: ProofGenerationContext,
        modelParams: OpenAiModelParams,
        previousProofVersions?: ProofVersion[] | undefined
    ): OpenAiGeneratedProof {
        return new OpenAiGeneratedProof(
            proof,
            proofGenerationContext,
            modelParams,
            this,
            previousProofVersions
        );
    }

    async generateFromChatImpl(
        chat: ChatHistory,
        params: OpenAiModelParams,
        choices: number
    ): Promise<string[]> {
        this.validateChoices(choices);

        const openai = new OpenAI({ apiKey: params.apiKey });
        this.debug.logEvent("Completion requested", { history: chat });

        try {
            const completion = await openai.chat.completions.create({
                messages: chat,
                model: params.modelName,
                n: choices,
                temperature: params.temperature,
                // eslint-disable-next-line @typescript-eslint/naming-convention
                max_tokens: params.maxTokensToGenerate,
            });
            return completion.choices.map(
                (choice: any) => choice.message.content
            );
        } catch (e) {
            throw OpenAiServiceInternal.repackKnownError(e, params);
        }
    }

    private static repackKnownError(
        caughtObject: any,
        params: OpenAiModelParams
    ): any {
        const error = caughtObject as Error;
        if (error === null) {
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
            const [
                modelsMaxContextLength,
                requestedTokens,
                requestedMessagesTokens,
                maxTokensToGenerate,
            ] = contextExceeded;
            const intro =
                "`tokensLimit` and `maxTokensToGenerate` are too large together";
            const explanation = `model's maximum context length is ${modelsMaxContextLength} tokens, but was requested ${requestedTokens} tokens = ${requestedMessagesTokens} in the messages + ${maxTokensToGenerate} in the completion`;
            return new ConfigurationError(`${intro}; ${explanation}`);
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
        /^The model `(.*)` does not exist or you do not have access to it\.$/;

    private static readonly incorrectApiKeyPattern =
        /^Incorrect API key provided: (.*)\.(.*)$/;

    private static readonly maximumContextLengthExceededPattern =
        /^This model's maximum context length is ([0-9]+) tokens\. However, you requested ([0-9]+) tokens \(([0-9]+) in the messages, ([0-9]+) in the completion\)\..*$/;
}
