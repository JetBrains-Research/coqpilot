import { AnalyzedChatHistory } from "../../../llm/llmServices/commonStructures/chat";
import { ErrorsHandlingMode } from "../../../llm/llmServices/commonStructures/errorsHandlingMode";
import {
    GeneratedRawContent,
    GeneratedRawContentItem,
} from "../../../llm/llmServices/commonStructures/generatedRawContent";
import { ProofGenerationMetadataHolder } from "../../../llm/llmServices/commonStructures/proofGenerationMetadata";
import { ProofVersion } from "../../../llm/llmServices/commonStructures/proofVersion";
import { SchedulersProviderBuilders } from "../../../llm/llmServices/commonStructures/schedulersProviders";
import { GeneratedProofImpl } from "../../../llm/llmServices/generatedProof";
import { LLMServiceImpl } from "../../../llm/llmServices/llmService";
import { LLMServiceInternal } from "../../../llm/llmServices/llmServiceInternal";
import {
    ModelParams,
    modelParamsSchema,
} from "../../../llm/llmServices/modelParams";
import { GenerationsLogger } from "../../../llm/llmServices/utils/generationsLogger/generationsLogger";
import { BasicModelParamsResolver } from "../../../llm/llmServices/utils/paramsResolvers/kit/basicModelParamsResolvers";
import { LLMServiceSerializer } from "../../../llm/llmServices/utils/serialization/llmServiceSerializer";
import { ProofGenerationContext } from "../../../llm/proofGenerationContext";
import { UserModelParams } from "../../../llm/userModelParams";

import { unsupported } from "../../../utils/errors/throwErrors";

import { provideTestSerializer } from "./testServiceSerializer";

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
    readonly name = "DummyLLMService";
    readonly identifier = undefined;

    protected readonly internal: DummyLLMServiceInternal;
    protected readonly modelParamsResolver = new BasicModelParamsResolver(
        modelParamsSchema,
        "ModelParams"
    );
    protected readonly serializer: LLMServiceSerializer;

    constructor(generationsLogger: GenerationsLogger) {
        super({
            errorsHandlingMode: ErrorsHandlingMode.RETHROW_ERRORS,
            debugLogs: true,
        });
        this.internal = new DummyLLMServiceInternal(this, generationsLogger);
        this.serializer = provideTestSerializer<GenerationsLogger>(
            generationsLogger,
            (generationsLogger) => new DummyLLMService(generationsLogger)
        );
    }

    dispose(): void {}

    generateFromChat(
        _analyzedChat: AnalyzedChatHistory,
        _params: ModelParams,
        _choices: number,
        _metadataHolder: ProofGenerationMetadataHolder | undefined
    ): Promise<string[]> {
        unsupported("I'm a teapot");
    }

    generateProof(
        _proofGenerationContext: ProofGenerationContext,
        _params: ModelParams,
        _choices: number,
        _metadataHolder: ProofGenerationMetadataHolder | undefined
    ): Promise<DummyGeneratedProof[]> {
        unsupported("I'm a teapot");
    }
}

export class DummyGeneratedProof extends GeneratedProofImpl<
    ModelParams,
    DummyLLMService,
    DummyGeneratedProof,
    DummyLLMServiceInternal
> {
    constructor(
        rawProof: GeneratedRawContentItem,
        proofGenerationContext: ProofGenerationContext,
        modelParams: ModelParams,
        llmServiceInternal: DummyLLMServiceInternal,
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

    fixProof(
        _diagnostic: string,
        _choices: number,
        _metadataHolder: ProofGenerationMetadataHolder | undefined
    ): Promise<DummyGeneratedProof[]> {
        unsupported("I'm a teapot");
    }
}

class DummyLLMServiceInternal extends LLMServiceInternal<
    ModelParams,
    DummyLLMService,
    DummyGeneratedProof,
    DummyLLMServiceInternal
> {
    constructGeneratedProof(
        _rawProof: GeneratedRawContentItem,
        _proofGenerationContext: ProofGenerationContext,
        _modelParams: ModelParams,
        _previousProofVersions?: ProofVersion[] | undefined
    ): DummyGeneratedProof {
        unsupported("I'm a teapot");
    }

    readonly modelsSchedulersProvider =
        SchedulersProviderBuilders.unlimitedParallelism(
            this.llmService.name,
            this.serviceSetup.enableModelsSchedulingDebugLogs
        );

    async generateFromChatImpl(
        _analyzedChat: AnalyzedChatHistory,
        _params: ModelParams,
        _choices: number
    ): Promise<GeneratedRawContent> {
        unsupported("I'm a teapot");
    }
}
