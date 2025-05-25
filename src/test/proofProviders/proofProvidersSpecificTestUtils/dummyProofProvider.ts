import { AnalyzedChatHistory } from "../../../proofProviders/impl/commonStructures/chat";
import { ErrorsHandlingMode } from "../../../proofProviders/impl/commonStructures/errorsHandlingMode";
import {
    GeneratedRawContent,
    GeneratedRawContentItem,
} from "../../../proofProviders/impl/commonStructures/generatedRawContent";
import { ProofGenerationMetadataHolder } from "../../../proofProviders/impl/commonStructures/proofGenerationMetadata";
import { ProofVersion } from "../../../proofProviders/impl/commonStructures/proofVersion";
import { SchedulersProviderBuilders } from "../../../proofProviders/impl/commonStructures/schedulersProviders";
import { GeneratedProof } from "../../../proofProviders/impl/generatedProof";
import {
    ModelParams,
    modelParamsSchema,
} from "../../../proofProviders/impl/modelParams";
import { ProofProvider } from "../../../proofProviders/impl/proofProvider";
import { ProofProviderInternal } from "../../../proofProviders/impl/proofProviderInternal";
import { GenerationsLogger } from "../../../proofProviders/impl/utils/generationsLogger/generationsLogger";
import { BasicModelParamsResolver } from "../../../proofProviders/impl/utils/paramsResolvers/kit/basicModelParamsResolvers";
import { ProofProviderSerializer } from "../../../proofProviders/impl/utils/serialization/proofProviderSerializer";
import { ProofGenerationContext } from "../../../proofProviders/proofGenerationContext";
import { UserModelParams } from "../../../proofProviders/userModelParams";

import { unsupported } from "../../../utils/errors/throwErrors";

import { provideTestSerializer } from "./testProofProviderSerializer";

/**
 * Mock implementation that always throws on any proof-generation call.
 * Its only mission is to exist: for example, it can be useful to build mock `ProofProviderRequest`-s.
 *
 * Additionally, it accepts `GenerationsLogger` from outside, so no resources are needed to be cleaned with `dispose`.
 */
export class DummyProofProvider extends ProofProvider<
    UserModelParams,
    ModelParams,
    DummyProofProvider,
    DummyGeneratedProof,
    DummyProofProviderInternal
> {
    readonly name = "DummyProofProvider";
    readonly identifier = undefined;

    protected readonly internal: DummyProofProviderInternal;
    protected readonly modelParamsResolver = new BasicModelParamsResolver(
        modelParamsSchema,
        "ModelParams"
    );
    protected readonly serializer: ProofProviderSerializer;

    constructor(generationsLogger: GenerationsLogger) {
        super({
            errorsHandlingMode: ErrorsHandlingMode.RETHROW_ERRORS,
            debugLogs: true,
        });
        this.internal = new DummyProofProviderInternal(this, generationsLogger);
        this.serializer = provideTestSerializer<GenerationsLogger>(
            generationsLogger,
            (generationsLogger) => new DummyProofProvider(generationsLogger)
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

export class DummyGeneratedProof extends GeneratedProof<
    ModelParams,
    DummyProofProvider,
    DummyGeneratedProof,
    DummyProofProviderInternal
> {
    constructor(
        rawProof: GeneratedRawContentItem,
        proofGenerationContext: ProofGenerationContext,
        modelParams: ModelParams,
        proofProviderInternal: DummyProofProviderInternal,
        previousProofVersions?: ProofVersion[]
    ) {
        super(
            rawProof,
            proofGenerationContext,
            modelParams,
            proofProviderInternal,
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

class DummyProofProviderInternal extends ProofProviderInternal<
    ModelParams,
    DummyProofProvider,
    DummyGeneratedProof,
    DummyProofProviderInternal
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
            this.proofProvider.name,
            this.proofProviderSetup.enableModelsSchedulingDebugLogs
        );

    async generateFromChatImpl(
        _analyzedChat: AnalyzedChatHistory,
        _params: ModelParams,
        _choices: number
    ): Promise<GeneratedRawContent> {
        unsupported("I'm a teapot");
    }
}
