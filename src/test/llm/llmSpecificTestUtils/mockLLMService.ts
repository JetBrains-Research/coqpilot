import {
    AnalyzedChatHistory,
    ChatHistory,
    ChatMessage,
} from "../../../llm/llmServices/chat";
import {
    ErrorsHandlingMode,
    GeneratedProof,
    LLMService,
    LLMServiceInternal,
    Proof,
    ProofVersion,
} from "../../../llm/llmServices/llmService";
import { ModelParams } from "../../../llm/llmServices/modelParams";
import { ProofGenerationContext } from "../../../llm/proofGenerationContext";
import { UserModelParams } from "../../../llm/userModelParams";

import { EventLogger } from "../../../logging/eventLogger";

export interface MockLLMUserModelParams extends UserModelParams {
    proofsToGenerate: string[];
    workerId?: number;
}

export interface MockLLMModelParams extends ModelParams {
    proofsToGenerate: string[];
    workerId: number;
    resolvedWithMockLLMService: boolean;
}

/*
 * This class implements `LLMService` the same way as most of the services do,
 * so as to reuse the default implementations as much as possible.
 * However, to make tests cover more corner cases, `MockLLMService` provides additional features.
 * Check the documentation of the methods below.
 */
export class MockLLMService extends LLMService {
    protected readonly internal: MockLLMServiceInternal;

    constructor(
        eventLogger?: EventLogger,
        debug: boolean = false,
        requestsLogsFilePath?: string
    ) {
        super("MockLLMService", eventLogger, debug, requestsLogsFilePath);
        this.internal = new MockLLMServiceInternal(
            this,
            this.eventLoggerGetter,
            this.requestsLoggerBuilder
        );
    }

    static readonly generationFromChatEvent = "mockllm-generation-from-chat";
    static readonly systemPromptToOverrideWith =
        "unique mock-llm system prompt";

    static readonly proofFixPrompt = "Generate `Fixed.` instead of proof.";
    static readonly fixedProofString = "Fixed.";

    /*
     * Use this method to make 1 next generation (for the specified worker) throw the specified error.
     * Workers are meant to be any external entities that would like to separate their behaviour.
     */
    throwErrorOnNextGeneration(error: Error, workerId: number = 0) {
        this.internal.throwErrorOnNextGenerationMap.set(workerId, error);
    }

    transformChatToSkipFirstNProofs(
        baseChat: ChatHistory,
        skipFirstNProofs: number
    ): ChatHistory {
        const controlMessage: ChatMessage = {
            role: "user",
            content: `SKIP_FIRST_PROOFS: ${skipFirstNProofs}`,
        };
        return [...baseChat, controlMessage];
    }

    /*
     * `MockLLMService` parameters resolution does 2 changes to `params`:
     * - overrides original `systemPrompt` to `this.systemPromptToOverrideWith`;
     * - resolves undefined `workerId` to 0;
     * - adds extra `resolvedWithMockLLMService: true` property.
     * Then `resolveParametersWithDefaults` is called.
     */
    resolveParameters(params: UserModelParams): ModelParams {
        const unresolvedParams = params as MockLLMUserModelParams;
        return this.resolveParametersWithDefaults({
            ...unresolvedParams,
            systemPrompt: MockLLMService.systemPromptToOverrideWith,
            workerId:
                unresolvedParams.workerId === undefined
                    ? 0
                    : unresolvedParams.workerId,
            resolvedWithMockLLMService: true,
        } as MockLLMUserModelParams);
    }
}

export class MockLLMGeneratedProof extends GeneratedProof {
    constructor(
        proof: Proof,
        proofGenerationContext: ProofGenerationContext,
        modelParams: MockLLMModelParams,
        llmServiceInternal: MockLLMServiceInternal,
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

    // This method just makes the default `generateNextVersion` visible to the tester.
    async generateNextVersion(
        analyzedChat: AnalyzedChatHistory,
        choices: number,
        errorsHandlingMode: ErrorsHandlingMode,
        postprocessProof: (proof: string) => string = (proof) => proof
    ): Promise<GeneratedProof[]> {
        return super.generateNextVersion(
            analyzedChat,
            choices,
            errorsHandlingMode,
            postprocessProof
        );
    }

    // The same trick to make the default `nextVersionCanBeGenerated` visible.
    nextVersionCanBeGenerated(): Boolean {
        return super.nextVersionCanBeGenerated();
    }
}

class MockLLMServiceInternal extends LLMServiceInternal {
    throwErrorOnNextGenerationMap: Map<number, Error | undefined> = new Map();

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

    /*
     * Generally, `generateFromChatImpl` simply returns first `choices` proofs from the `MockLLMModelParams.proofsToGenerate`.
     * Each `generateFromChatImpl` call sends logic `this.generationFromChatEvent` event to the `eventLogger`.
     * Special behaviour:
     * - If `throwErrorOnNextGenereation` was registered for `MockLLMModelParams.workerId`,
     *   `generateFromChatImpl` throws this error and then resets this behaviour for the next call.
     * - If `chat` contains special control message (see `transformChatToSkipFirstNProofs`),
     *   several proofs from the beggining of `MockLLMModelParams.proofsToGenerate` will be skipped.
     *   Practically, it provides a way to generate different proofs depending on the `chat` (while `modelParams` stay the same).
     * - If `chat` contains `this.proofFixPrompt` in any of its messages,
     *   then all the generated proofs will be equal to `this.fixedProofString`.
     */
    async generateFromChatImpl(
        chat: ChatHistory,
        params: ModelParams,
        choices: number
    ): Promise<string[]> {
        this.eventLogger?.logLogicEvent(
            MockLLMService.generationFromChatEvent,
            chat
        );
        const mockLLMServiceParams = params as MockLLMModelParams;

        const throwError = this.throwErrorOnNextGenerationMap.get(
            mockLLMServiceParams.workerId
        );
        if (throwError !== undefined) {
            try {
                throw throwError;
            } finally {
                this.throwErrorOnNextGenerationMap.set(
                    mockLLMServiceParams.workerId,
                    undefined
                );
            }
        }

        const proofFixPromptInChat = chat.find(
            (message) => message.content === MockLLMService.proofFixPrompt
        );
        if (proofFixPromptInChat !== undefined) {
            return Array(choices).fill(MockLLMService.fixedProofString);
        }

        const lastChatMessage = chat[chat.length - 1];
        const skipFirstNProofsParsed =
            this.parseSkipFirstNProofsIfMatches(lastChatMessage);
        const skipFirstNProofs =
            skipFirstNProofsParsed !== undefined ? skipFirstNProofsParsed : 0;

        const proofsLength =
            mockLLMServiceParams.proofsToGenerate.length - skipFirstNProofs;
        if (choices > proofsLength) {
            throw Error(
                `\`choices = ${choices}\` > \`available proofs length = ${proofsLength}\``
            );
        }

        return mockLLMServiceParams.proofsToGenerate.slice(
            skipFirstNProofs,
            skipFirstNProofs + choices
        );
    }

    private readonly skipFirstNProofsContentPattern =
        /^SKIP_FIRST_PROOFS: (.*)$/;

    private parseSkipFirstNProofsIfMatches(
        message: ChatMessage
    ): number | undefined {
        const match = message.content.match(
            this.skipFirstNProofsContentPattern
        );
        if (!match) {
            return undefined;
        }
        return parseInt(match[1]);
    }
}