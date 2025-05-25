import { AnalyzedChatHistory } from "../../../proofProviders/impl/commonStructures/chat";
import {
    GeneratedRawContent,
    GeneratedRawContentItem,
} from "../../../proofProviders/impl/commonStructures/generatedRawContent";
import { ProofVersion } from "../../../proofProviders/impl/commonStructures/proofVersion";
import { SchedulersProvider } from "../../../proofProviders/impl/commonStructures/schedulersProviders";
import { GeneratedProof } from "../../../proofProviders/impl/generatedProof";
import { ProofProvider } from "../../../proofProviders/impl/proofProvider";
import { ProofProviderInternal } from "../../../proofProviders/impl/proofProviderInternal";
import { ProofGenerationContext } from "../../../proofProviders/proofGenerationContext";

import { BenchmarkingLogger } from "../logging/benchmarkingLogger";

import {
    BenchTestModelParams,
    BenchTestModelParamsResolver,
    BenchTestUserModelParams,
} from "./benchTestModelParams";
import {
    BenchTestServiceParams,
    GenerateRawProofsType,
    ResolvedBenchTestServiceParams,
    resolveBenchTestServiceParamsWithDefaults,
} from "./benchTestServiceParams";
import { BenchTestServiceSerializer } from "./benchTestServiceSerializer";

export class BenchTestService extends ProofProvider<
    BenchTestUserModelParams,
    BenchTestModelParams,
    BenchTestService,
    BenchTestGeneratedProof,
    BenchTestServiceInternal
> {
    readonly name = "BenchTestService";
    readonly shortName = "BenchTest";
    readonly identifier = undefined;

    protected readonly internal: BenchTestServiceInternal;
    protected readonly modelParamsResolver = new BenchTestModelParamsResolver();
    protected readonly serializer;

    constructor(
        proofProviderParams: BenchTestServiceParams = {},
        resolveServiceParamsWithDefaults: (
            proofProviderParams: BenchTestServiceParams
        ) => ResolvedBenchTestServiceParams = resolveBenchTestServiceParamsWithDefaults
    ) {
        const resolvedServiceParams =
            resolveServiceParamsWithDefaults(proofProviderParams);
        super(resolvedServiceParams);
        this.internal = new BenchTestServiceInternal(
            this,
            resolvedServiceParams.logger,
            resolvedServiceParams.generateRawProofs,
            resolvedServiceParams.getSchedulersProvider
        );
        this.serializer = new BenchTestServiceSerializer(resolvedServiceParams);
    }
}

export class BenchTestGeneratedProof extends GeneratedProof<
    BenchTestModelParams,
    BenchTestService,
    BenchTestGeneratedProof,
    BenchTestServiceInternal
> {
    constructor(
        rawProof: GeneratedRawContentItem,
        proofGenerationContext: ProofGenerationContext,
        modelParams: BenchTestModelParams,
        proofProviderInternal: BenchTestServiceInternal
    ) {
        super(
            rawProof,
            proofGenerationContext,
            modelParams,
            proofProviderInternal
        );
    }
}

class BenchTestServiceInternal extends ProofProviderInternal<
    BenchTestModelParams,
    BenchTestService,
    BenchTestGeneratedProof,
    BenchTestServiceInternal
> {
    constructor(
        readonly proofProvider: BenchTestService,
        private readonly logger: BenchmarkingLogger,
        private readonly generateRawProofs: GenerateRawProofsType,
        private readonly getSchedulersProvider: (
            proofProvider: BenchTestService
        ) => SchedulersProvider
    ) {
        super(proofProvider);
    }

    constructGeneratedProof(
        rawProof: GeneratedRawContentItem,
        proofGenerationContext: ProofGenerationContext,
        modelParams: BenchTestModelParams,
        _previousProofVersions?: ProofVersion[]
    ): BenchTestGeneratedProof {
        return new BenchTestGeneratedProof(
            rawProof,
            proofGenerationContext,
            modelParams,
            this
        );
    }

    readonly modelsSchedulersProvider = this.getSchedulersProvider(
        this.proofProvider
    );

    async generateFromChatImpl(
        analyzedChat: AnalyzedChatHistory,
        params: BenchTestModelParams,
        choices: number
    ): Promise<GeneratedRawContent> {
        const rawContentItems = await this.generateRawProofs(
            analyzedChat,
            params,
            choices,
            this.logger
        );
        return ProofProviderInternal.aggregateToGeneratedRawContent(
            rawContentItems,
            analyzedChat.estimatedTokens.messagesTokens,
            undefined
        );
    }
}
