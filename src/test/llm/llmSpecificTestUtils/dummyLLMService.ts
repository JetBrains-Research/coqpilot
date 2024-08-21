import {
    AnalyzedChatHistory,
    ChatHistory,
} from "../../../llm/llmServices/chat";
import {
    ErrorsHandlingMode,
    GeneratedProofImpl,
    LLMServiceImpl,
    ProofVersion,
} from "../../../llm/llmServices/llmService";
import { LLMServiceInternal } from "../../../llm/llmServices/llmServiceInternal";
import {
    ModelParams,
    modelParamsSchema,
} from "../../../llm/llmServices/modelParams";
import { GenerationsLogger } from "../../../llm/llmServices/utils/generationsLogger/generationsLogger";
import { BasicModelParamsResolver } from "../../../llm/llmServices/utils/paramsResolvers/basicModelParamsResolvers";
import { ProofGenerationContext } from "../../../llm/proofGenerationContext";
import { UserModelParams } from "../../../llm/userModelParams";

/**
 * Mock implementation that always throws on any proof-generation call.
 * Its only mission is to exist: for example, it can be useful to build mock `LLMServiceRequest`-s.
 *
 * Additionally, it accepts `GenerationsLogger` from outside, so no resources are needed to be cleaned with `dispose`.
 */
export class DummyLLMService extends LLMServiceImpl<
    UserModelParams,
    ModelParams,
    DummyLLMService,
    DummyGeneratedProof,
    DummyLLMServiceInternal
> {
    protected readonly internal: DummyLLMServiceInternal;
    protected readonly modelParamsResolver = new BasicModelParamsResolver(
        modelParamsSchema,
        "ModelParams"
    );

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
    ): Promise<DummyGeneratedProof[]> {
        throw Error("I'm a teapot");
    }
}

export class DummyGeneratedProof extends GeneratedProofImpl<
    ModelParams,
    DummyLLMService,
    DummyGeneratedProof,
    DummyLLMServiceInternal
> {
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
    ): Promise<DummyGeneratedProof[]> {
        throw Error("I'm a teapot");
    }
}

class DummyLLMServiceInternal extends LLMServiceInternal<
    ModelParams,
    DummyLLMService,
    DummyGeneratedProof,
    DummyLLMServiceInternal
> {
    constructGeneratedProof(
        _proof: string,
        _proofGenerationContext: ProofGenerationContext,
        _modelParams: ModelParams,
        _previousProofVersions?: ProofVersion[] | undefined
    ): DummyGeneratedProof {
        throw Error("I'm a teapot");
    }

    async generateFromChatImpl(
        _analyzedChat: AnalyzedChatHistory,
        _params: ModelParams,
        _choices: number
    ): Promise<GeneratedRawContent> {
        throw Error("I'm a teapot");
    }
}
