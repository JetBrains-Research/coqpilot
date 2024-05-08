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
        this.validateChoices(choices);
        const openAiParams = params as OpenAiModelParams;
        this.validateTemperature(openAiParams);

        const openai = new OpenAI({ apiKey: openAiParams.apiKey });
        this.debug.logEvent("Completion requested", { history: chat });

        try {
            const completion = await openai.chat.completions.create({
                messages: chat,
                model: openAiParams.modelName,
                n: choices,
                temperature: openAiParams.temperature,
                // eslint-disable-next-line @typescript-eslint/naming-convention
                max_tokens: openAiParams.maxTokensToGenerate,
            });
            return completion.choices.map(
                (choice: any) => choice.message.content
            );
        } catch (e) {
            throw this.repackKnownError(e, openAiParams);
        }
    }

    private validateTemperature(openAiParams: OpenAiModelParams) {
        const temperature = openAiParams.temperature;
        if (temperature < 0 || temperature > 2) {
            throw new ConfigurationError(
                `invalid temperature "${temperature}", it should be in range between 0 and 2`
            );
        }
    }

    private repackKnownError(
        caughtObject: any,
        openAiParams: OpenAiModelParams
    ): any {
        const error = caughtObject as Error;
        if (error === null) {
            return caughtObject;
        }
        const errorMessage = error.message;

        if (
            this.matchesPattern(
                OpenAiServiceInternal.unknownModelNamePattern,
                errorMessage
            )
        ) {
            return new ConfigurationError(
                `invalid model name "${openAiParams.modelName}", such model does not exist or you do not have access to it`
            );
        }
        if (
            this.matchesPattern(
                OpenAiServiceInternal.incorrectApiKeyPattern,
                errorMessage
            )
        ) {
            return new ConfigurationError(
                `incorrect api key "${openAiParams.apiKey}" (check your API key at https://platform.openai.com/account/api-keys)`
            );
        }
        return error;
    }

    private matchesPattern(pattern: RegExp, text: string): boolean {
        return text.match(pattern) !== null;
    }

    private static unknownModelNamePattern =
        /^The model `(.*)` does not exist or you do not have access to it\.$/;

    private static incorrectApiKeyPattern =
        /^Incorrect API key provided: (.*)\.(.*)$/;
}
