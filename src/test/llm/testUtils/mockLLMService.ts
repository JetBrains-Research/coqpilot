import { ChatHistory } from "../../../llm/llmServices/chat";
import {
    GeneratedProof,
    LLMService,
    Proof,
    ProofVersion,
} from "../../../llm/llmServices/llmService";
import { ModelParams } from "../../../llm/llmServices/modelParams";
import { ProofGenerationContext } from "../../../llm/proofGenerationContext";
import { UserModelParams } from "../../../llm/userModelParams";

import { EventLogger } from "../../../logging/eventLogger";

export interface MockLLMUserModelParams extends UserModelParams {
    proofsToGenerate: string[];
    throwError?: Error;
}

export interface MockLLMModelParams extends ModelParams {
    proofsToGenerate: string[];
    throwError?: Error;
    resolvedWithMockLLMService: boolean;
}

export class MockLLMService extends LLMService {
    constructor(requestsLogsFilePath: string, eventLogger?: EventLogger) {
        super("MockLLMService", requestsLogsFilePath, eventLogger);
    }

    readonly generationFromChatEvent = "mockllm-generation-from-chat";
    readonly systemPromptToOverrideWith = "unique mock-llm system prompt";

    constructGeneratedProof(
        proof: string,
        proofGenerationContext: ProofGenerationContext,
        modelParams: ModelParams,
        previousProofVersions?: ProofVersion[] | undefined
    ): GeneratedProof {
        return new MockLLMGeneratedProof(
            proof,
            proofGenerationContext,
            modelParams as MockLLMModelParams,
            this,
            previousProofVersions
        );
    }

    protected async generateFromChatImpl(
        chat: ChatHistory,
        params: ModelParams,
        choices: number
    ): Promise<string[]> {
        this.eventLogger?.logLogicEvent(this.generationFromChatEvent, chat);

        const mockLLMServiceParams = params as MockLLMModelParams;
        if (mockLLMServiceParams.throwError !== undefined) {
            throw mockLLMServiceParams.throwError;
        }

        const proofsLength = mockLLMServiceParams.proofsToGenerate.length;
        if (choices > proofsLength) {
            throw Error(
                `\`choices = ${choices}\` > \`proofsToGenerate.length = ${proofsLength}\``
            );
        }
        return mockLLMServiceParams.proofsToGenerate.splice(choices);
    }

    resolveParameters(params: UserModelParams): ModelParams {
        const unresolvedParams = params as MockLLMUserModelParams;
        unresolvedParams.systemPrompt = this.systemPromptToOverrideWith;
        return this.resolveParametersWithDefaults({
            ...unresolvedParams,
            resolvedWithMockLLMService: true,
        } as MockLLMUserModelParams);
    }
}

export class MockLLMGeneratedProof extends GeneratedProof {
    constructor(
        proof: Proof,
        proofGenerationContext: ProofGenerationContext,
        modelParams: MockLLMModelParams,
        llmService: MockLLMService,
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
