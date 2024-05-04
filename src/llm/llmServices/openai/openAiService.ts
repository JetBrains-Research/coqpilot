import OpenAI from "openai";

import { EventLogger } from "../../../logging/eventLogger";
import { ConfigurationError } from "../../llmServiceErrors";
import { ProofGenerationContext } from "../../proofGenerationContext";
import { ChatHistory } from "../chat";
import {
    GeneratedProof,
    LLMService,
    LLMServiceInternal,
    ProofVersion,
} from "../llmService";
import { ModelParams, OpenAiModelParams } from "../modelParams";

export class OpenAiService extends LLMService {
    protected readonly internal: OpenAiServiceInternal;

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

export class OpenAiGeneratedProof extends GeneratedProof {
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

class OpenAiServiceInternal extends LLMServiceInternal {
    constructGeneratedProof(
        proof: string,
        proofGenerationContext: ProofGenerationContext,
        modelParams: ModelParams,
        previousProofVersions?: ProofVersion[] | undefined
    ): GeneratedProof {
        return new OpenAiGeneratedProof(
            proof,
            proofGenerationContext,
            modelParams as OpenAiModelParams,
            this,
            previousProofVersions
        );
    }

    async generateFromChatImpl(
        chat: ChatHistory,
        params: ModelParams,
        choices: number
    ): Promise<string[]> {
        // TODO: support retries
        if (choices <= 0) {
            throw new ConfigurationError(`bad choices: ${choices} <= 0`);
        }
        const openAiParams = params as OpenAiModelParams;
        const openai = new OpenAI({ apiKey: openAiParams.apiKey });
        this.debug.logEvent("Completion requested", { history: chat });

        const completion = await openai.chat.completions.create({
            messages: chat,
            model: openAiParams.modelName,
            n: choices,
            temperature: openAiParams.temperature,
            // eslint-disable-next-line @typescript-eslint/naming-convention
            max_tokens: openAiParams.newMessageMaxTokens,
        });

        return completion.choices.map((choice: any) => choice.message.content);
    }
}
