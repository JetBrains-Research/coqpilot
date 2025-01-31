import { EventLogger } from "../logging/eventLogger";

import { LLMServices } from "./llmServices";
import { GeneratedProof } from "./llmServices/generatedProof";
import { LLMService } from "./llmServices/llmService";
import { ModelParams, ModelsParams } from "./llmServices/modelParams";
import { ProofGenerationContext } from "./proofGenerationContext";

type GeneratedProofsBatch = GeneratedProof[];
type ProofsGenerationHook = () => Promise<GeneratedProofsBatch>;

export class LLMSequentialIterator
    implements AsyncIterator<GeneratedProofsBatch>
{
    private proofsGenerationHook: ProofsGenerationHook[];
    private fetchedResults: GeneratedProofsBatch[];

    private hooksIndex: number;
    private insideBatchIndex: number;

    constructor(
        proofGenerationContext: ProofGenerationContext,
        modelsParams: ModelsParams,
        services: LLMServices,
        private eventLogger?: EventLogger
    ) {
        this.hooksIndex = 0;
        this.insideBatchIndex = 0;
        this.proofsGenerationHook = this.createHooks(
            proofGenerationContext,
            modelsParams,
            services
        );
        this.fetchedResults = new Array<GeneratedProofsBatch>(
            this.proofsGenerationHook.length
        );
    }

    // TODO: Implement a smarter way of ordering the services
    private createHooks(
        proofGenerationContext: ProofGenerationContext,
        modelsParams: ModelsParams,
        services: LLMServices
    ): ProofsGenerationHook[] {
        return [
            ...this.createLLMServiceHooks(
                proofGenerationContext,
                modelsParams.predefinedProofsModelParams,
                services.predefinedProofsService,
                "predefined-proofs"
            ),
            // Here DeepSeek service is reordered to the beginning
            // of the list, due to it's strong performance and
            // low costs. Refer to discussion:
            // https://github.com/JetBrains-Research/coqpilot/pull/56#discussion_r1935180516
            ...this.createLLMServiceHooks(
                proofGenerationContext,
                modelsParams.deepSeekParams,
                services.deepSeekService,
                "deepseek"
            ),
            ...this.createLLMServiceHooks(
                proofGenerationContext,
                modelsParams.openAiParams,
                services.openAiService,
                "openai"
            ),
            ...this.createLLMServiceHooks(
                proofGenerationContext,
                modelsParams.grazieParams,
                services.grazieService,
                "grazie"
            ),
            ...this.createLLMServiceHooks(
                proofGenerationContext,
                modelsParams.lmStudioParams,
                services.lmStudioService,
                "lm-studio"
            ),
        ];
    }

    private createLLMServiceHooks<ResolvedModelParams extends ModelParams>(
        proofGenerationContext: ProofGenerationContext,
        allModelParamsForService: ResolvedModelParams[],
        llmService: LLMService<any, ResolvedModelParams>,
        serviceLoggingName: string
    ): ProofsGenerationHook[] {
        const hooks = [];
        for (const modelParams of allModelParamsForService) {
            hooks.push(() => {
                this.eventLogger?.log(
                    `${serviceLoggingName}-fetch-started`,
                    `Completion from ${serviceLoggingName}`,
                    modelParams
                );
                return llmService.generateProof(
                    proofGenerationContext,
                    modelParams
                );
            });
        }
        return hooks;
    }

    [Symbol.asyncIterator]() {
        return this;
    }

    private async prepareFetched(): Promise<boolean> {
        if (this.hooksIndex >= this.proofsGenerationHook.length) {
            return true;
        }

        if (this.fetchedResults[this.hooksIndex] === undefined) {
            this.fetchedResults[this.hooksIndex] =
                await this.proofsGenerationHook[this.hooksIndex]();
        }

        if (
            this.insideBatchIndex >= this.fetchedResults[this.hooksIndex].length
        ) {
            this.hooksIndex += 1;
            this.insideBatchIndex = 0;
            return this.prepareFetched();
        }

        return false;
    }

    async next(): Promise<IteratorResult<GeneratedProofsBatch, undefined>> {
        const finished = await this.prepareFetched();
        if (finished) {
            return { done: true, value: undefined };
        }

        const proofs = this.fetchedResults[this.hooksIndex].slice(
            this.insideBatchIndex
        );
        this.insideBatchIndex = this.fetchedResults[this.hooksIndex].length;

        return { done: false, value: proofs };
    }

    async nextProof(): Promise<IteratorResult<GeneratedProof, undefined>> {
        const finished = await this.prepareFetched();
        if (finished) {
            return { done: true, value: undefined };
        }

        const proof =
            this.fetchedResults[this.hooksIndex][this.insideBatchIndex];
        this.insideBatchIndex += 1;

        return { done: false, value: proof };
    }
}
