import {
    AnalyzedChatHistory,
    ChatHistory,
} from "../../../llm/llmServices/chat";
import {
    ErrorsHandlingMode,
    GeneratedProof,
    LLMService,
    LLMServiceInternal,
    ProofVersion,
} from "../../../llm/llmServices/llmService";
import { ModelParams } from "../../../llm/llmServices/modelParams";
import { GenerationsLogger } from "../../../llm/llmServices/utils/generationsLogger/generationsLogger";
import { ProofGenerationContext } from "../../../llm/proofGenerationContext";

/**
 * Mock implementation that always throws on any proof-generation call.
 * Its only mission is to exist: for example, it can be useful to build mock `LLMServiceRequest`-s.
 *
 * Additionally, it accepts `GenerationsLogger` from outside, so no resources are needed to be cleaned with `dispose`.
 */
export class DummyLLMService extends LLMService {
    protected readonly internal: LLMServiceInternal;

    constructor(generationsLogger: GenerationsLogger) {
        super("DummyLLMService", undefined, true, undefined);
        this.internal = new DummyLLMServiceInternal(
            this,
            this.eventLoggerGetter,
            () => generationsLogger
        );
    }

    dispose(): void {}

    generateFromChat(
        _analyzedChat: AnalyzedChatHistory,
        _params: ModelParams,
        _choices: number,
        _errorsHandlingMode?: ErrorsHandlingMode
    ): Promise<string[]> {
        throw Error("I'm a teapot");
    }

    generateProof(
        _proofGenerationContext: ProofGenerationContext,
        _params: ModelParams,
        _choices: number,
        _errorsHandlingMode?: ErrorsHandlingMode
    ): Promise<GeneratedProof[]> {
        throw Error("I'm a teapot");
    }
}

export class DummyGeneratedProof extends GeneratedProof {
    constructor(
        proof: string,
        proofGenerationContext: ProofGenerationContext,
        modelParams: ModelParams,
        llmServiceInternal: DummyLLMServiceInternal,
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

    fixProof(
        _diagnostic: string,
        _choices?: number,
        _errorsHandlingMode?: ErrorsHandlingMode
    ): Promise<GeneratedProof[]> {
        throw Error("I'm a teapot");
    }
}

class DummyLLMServiceInternal extends LLMServiceInternal {
    constructGeneratedProof(
        _proof: string,
        _proofGenerationContext: ProofGenerationContext,
        _modelParams: ModelParams,
        _previousProofVersions?: ProofVersion[] | undefined
    ): GeneratedProof {
        throw Error("I'm a teapot");
    }

    async generateFromChatImpl(
        _chat: ChatHistory,
        _params: ModelParams,
        _choices: number
    ): Promise<string[]> {
        throw Error("I'm a teapot");
    }
}
