import { ProofGenerationContext } from "./llmServices/modelParamsInterfaces";
import { EventLogger } from "../logging/eventLogger";
import { ModelsParams, LLMServices } from "./configurations";

export type Proof = string;
export type ProofBatch = Proof[];

type ProofsGenerationHook = () => Promise<string[]>;

export class LLMSequentialIterator implements AsyncIterator<ProofBatch> {
    private proofsGenerationHook: ProofsGenerationHook[];
    private fetchedResults: ProofBatch[];

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
        this.fetchedResults = new Array<ProofBatch>(this.proofsGenerationHook.length);
    }

    private createHooks(
        proofGenerationContext: ProofGenerationContext, 
        modelsParams: ModelsParams,
        services: LLMServices
    ): ProofsGenerationHook[] {
        const proofsGenerationHooks: ProofsGenerationHook[] = [];
        for (const params of modelsParams.predefinedProofsModelParams) {
            proofsGenerationHooks.push(
                () => {
                    this.eventLogger?.log("predefined-proofs-fetch-started", JSON.stringify(params));
                    return services.predefinedProofsService.generateProof(
                        proofGenerationContext, 
                        params
                    );
                }
            );
        }

        for (const params of modelsParams.openAiParams) {
            proofsGenerationHooks.push(
                () => {
                    this.eventLogger?.log("openai-fetch-started", JSON.stringify(params));
                    return services.openAiService.generateProof(
                        proofGenerationContext, 
                        params
                    );
                }
            );
        }

        for (const params of modelsParams.grazieParams) {
            proofsGenerationHooks.push(
                () => {
                    this.eventLogger?.log("grazie-fetch-started", JSON.stringify(params));
                    return services.grazieService.generateProof(
                        proofGenerationContext, 
                        params
                    );
                }
            );
        }

        return proofsGenerationHooks;
    }

    [Symbol.asyncIterator]() {
        return this;
    }

    private async prepareFetched(): Promise<boolean> {
        if (this.hooksIndex >= this.proofsGenerationHook.length) {
            return true;
        }

        if (this.fetchedResults[this.hooksIndex] === undefined) {
            this.fetchedResults[this.hooksIndex] = await this.proofsGenerationHook[this.hooksIndex]();
        }

        if (this.insideBatchIndex >= this.fetchedResults[this.hooksIndex].length) {
            this.hooksIndex += 1;
            this.insideBatchIndex = 0;
            return this.prepareFetched();
        }

        return false;
    }

    async next(): Promise<IteratorResult<ProofBatch, any>> {
        const finished = await this.prepareFetched();
        if (finished) {
            return { done: true, value: undefined };
        }

        const proofs = this.fetchedResults[this.hooksIndex].slice(this.insideBatchIndex);
        this.insideBatchIndex = this.fetchedResults[this.hooksIndex].length;

        return { done: false, value: proofs };
    }

    async nextProof(): Promise<IteratorResult<Proof, any>> {
        const finished = await this.prepareFetched();
        if (finished) {
            return { done: true, value: undefined };
        }

        const proof = this.fetchedResults[this.hooksIndex][this.insideBatchIndex];
        this.insideBatchIndex += 1;

        return { done: false, value: proof };
    }
}