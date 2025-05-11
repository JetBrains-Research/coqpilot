import { AnalyzedChatHistory } from "../../../../../llm/llmServices/commonStructures/chat";
import {
    GeneratedRawContent,
    GeneratedRawContentItem,
} from "../../../../../llm/llmServices/commonStructures/generatedRawContent";
import { ProofVersion } from "../../../../../llm/llmServices/commonStructures/proofVersion";
import { SchedulersProvider } from "../../../../../llm/llmServices/commonStructures/schedulersProviders";
import { GeneratedProofImpl } from "../../../../../llm/llmServices/generatedProof";
import { LLMServiceImpl } from "../../../../../llm/llmServices/llmService";
import { LLMServiceInternal } from "../../../../../llm/llmServices/llmServiceInternal";
import { ProofGenerationContext } from "../../../../../llm/proofGenerationContext";

import { BenchmarkingLogger } from "../../../logging/benchmarkingLogger";

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

export class BenchTestService extends LLMServiceImpl<
    BenchTestUserModelParams,
    BenchTestModelParams,
    BenchTestService,
    BenchTestGeneratedProof,
    BenchTestServiceInternal
> {
    readonly fullName = "BenchTestService";
    readonly shortName = "BenchTest";

    protected readonly internal: BenchTestServiceInternal;

    constructor(
        serviceParams: BenchTestServiceParams = {},
        resolveServiceParamsWithDefaults: (
            serviceParams: BenchTestServiceParams
        ) => ResolvedBenchTestServiceParams = resolveBenchTestServiceParamsWithDefaults
    ) {
        const resolvedServiceParams =
            resolveServiceParamsWithDefaults(serviceParams);
        super(resolvedServiceParams);
        this.internal = new BenchTestServiceInternal(
            this,
            resolvedServiceParams.logger,
            resolvedServiceParams.generateRawProofs,
            resolvedServiceParams.getSchedulersProvider
        );
    }

    protected readonly modelParamsResolver = new BenchTestModelParamsResolver();
}

export class BenchTestGeneratedProof extends GeneratedProofImpl<
    BenchTestModelParams,
    BenchTestService,
    BenchTestGeneratedProof,
    BenchTestServiceInternal
> {
    constructor(
        rawProof: GeneratedRawContentItem,
        proofGenerationContext: ProofGenerationContext,
        modelParams: BenchTestModelParams,
        llmServiceInternal: BenchTestServiceInternal
    ) {
        super(
            rawProof,
            proofGenerationContext,
            modelParams,
            llmServiceInternal
        );
    }
}

class BenchTestServiceInternal extends LLMServiceInternal<
    BenchTestModelParams,
    BenchTestService,
    BenchTestGeneratedProof,
    BenchTestServiceInternal
> {
    constructor(
        readonly llmService: BenchTestService,
        private readonly logger: BenchmarkingLogger,
        private readonly generateRawProofs: GenerateRawProofsType,
        private readonly getSchedulersProvider: (
            service: BenchTestService
        ) => SchedulersProvider
    ) {
        super(llmService);
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
        this.llmService
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
        return LLMServiceInternal.aggregateToGeneratedRawContent(
            rawContentItems,
            analyzedChat.estimatedTokens.messagesTokens,
            undefined
        );
    }
}
