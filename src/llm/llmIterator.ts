import { 
    ProofGenerationContext, 
    OpenAiModelParams,
    GrazieModelParams,
    PredefinedProofsModelParams
} from "./llmService/modelParamsInterfaces";
import { GrazieService } from "./llmService/grazie/grazieService";
import { OpenAiService } from "./llmService/openai/openAiService";
import { 
    PredefinedProofsService 
} from "./llmService/predefinedProofs/predefinedProofsService";
import { EventLogger } from "../logging/eventLogger";


export type Proof = string;
export type ProofBatch = Proof[];

export interface LLMServices {
    openAiService: OpenAiService;
    grazieService: GrazieService;
    predefinedProofsService: PredefinedProofsService;
}

export interface ModelsParams {
    openAiParams: OpenAiModelParams[];
    grazieParams: GrazieModelParams[];
    predefinedProofsModelParams: PredefinedProofsModelParams[];
}

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

        if (this.insideBatchIndex >= this.fetchedResults[this.hooksIndex].length) {
            this.hooksIndex += 1;
            this.insideBatchIndex = 0;
            return this.prepareFetched();
        }

        if (this.fetchedResults[this.hooksIndex] === undefined) {
            this.fetchedResults[this.hooksIndex] = await this.proofsGenerationHook[this.hooksIndex]();
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