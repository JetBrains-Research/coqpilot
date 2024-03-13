import { EventLogger } from "../logging/eventLogger";

import { LLMServices } from "./llmServices";
import { GeneratedProof, LLMService } from "./llmServices/llmService";
import { ProofGenerationContext } from "./proofGenerationContext";
import {
    PredefinedProofsUserModelParams,
    UserModelParams,
    UserModelsParams,
} from "./userModelParams";

type GeneratedProofsBatch = GeneratedProof[];
type ProofsGenerationHook = () => Promise<GeneratedProofsBatch>;

export class LLMSequentialIterator
    implements AsyncIterator<GeneratedProofsBatch>
{
    private proofsGenerationHook: ProofsGenerationHook[];
    private fetchedResults: GeneratedProofsBatch[];

    private hooksIndex: number;
    private insideBatchIndex: number;

    private readonly defaultGenerationChoices = 10;

    constructor(
        proofGenerationContext: ProofGenerationContext,
        modelsParams: UserModelsParams,
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

    private createHooks(
        proofGenerationContext: ProofGenerationContext,
        modelsParams: UserModelsParams,
        services: LLMServices
    ): ProofsGenerationHook[] {
        return [
            ...this.createLLMServiceHooks(
                proofGenerationContext,
                modelsParams.predefinedProofsModelParams,
                services.predefinedProofsService,
                "predefined-proofs",
                (params) =>
                    (params as PredefinedProofsUserModelParams).tactics.length
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

    private createLLMServiceHooks(
        proofGenerationContext: ProofGenerationContext,
        allModelParamsForService: UserModelParams[],
        llmService: LLMService,
        serviceLoggingName: string,
        resolveChoices: (userModelParams: UserModelParams) => number = (_) =>
            this.defaultGenerationChoices
    ): ProofsGenerationHook[] {
        const hooks = [];
        for (const userModelParams of allModelParamsForService) {
            hooks.push(() => {
                const resolvedParams =
                    llmService.resolveParameters(userModelParams);
                this.eventLogger?.log(
                    `${serviceLoggingName}-fetch-started`,
                    `Completion from ${serviceLoggingName}`,
                    resolvedParams
                );
                return llmService.generateProof(
                    proofGenerationContext,
                    resolvedParams,
                    userModelParams.choices ?? resolveChoices(userModelParams)
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

    async next(): Promise<IteratorResult<GeneratedProofsBatch, any>> {
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

    async nextProof(): Promise<IteratorResult<GeneratedProof, any>> {
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
