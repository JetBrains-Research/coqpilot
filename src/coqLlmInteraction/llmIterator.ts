import { LLMInterface } from "./llmInterface";
import { LLMPrompt, LlmPromptBase } from './llmPromptInterface';
import { ProgressBar } from "../extension/progressBar";
import logger from "../extension/logger";
import { ConfigWrapperInterface } from "../extension/config";

export type Proof = string;
export type ProofBatch = Proof[];

export class LLMIterator implements AsyncIterator<Proof> {
    private models: LLMInterface[];
    private fetchedResults: ProofBatch[];

    private modelIndex: number;
    private proofIndex: number;
    private config: ConfigWrapperInterface;
    private progressBar: ProgressBar;

    constructor(models: LLMInterface[], config: ConfigWrapperInterface, progressBar: ProgressBar) {
        this.models = models;
        this.fetchedResults = new Array<ProofBatch>(models.length);
        this.modelIndex = 0;
        this.proofIndex = 0;
        this.config = config;
        this.progressBar = progressBar;
    }

    [Symbol.asyncIterator]() {
        return this;
    }

    restart(): void {
        this.modelIndex = 0;
        this.proofIndex = 0;
        this.fetchedResults = new Array<ProofBatch>(this.models.length);
    }

    postProcessProof(proof: Proof): Proof {
        let result = LlmPromptBase.removeBackticks(proof);
        // Surround with curly braces and remove Proof. and Qed.
        result = LlmPromptBase.thrProofToBullet(result);

        return result;
    } 

    initHistory(llmPrompt: LLMPrompt): void {
        this.models.forEach(model => model.initHistory(llmPrompt));
    }

    async next(...args: any[] | [undefined]): Promise<IteratorResult<string, any>> {
        const message = args[0] as string;
        if (this.modelIndex >= this.models.length) {
            return { done: true, value: undefined };
        }

        if (this.fetchedResults[this.modelIndex] === undefined) {
            if (!message) {
                throw new Error("Iterated without a value");
            }
            this.fetchedResults[this.modelIndex] = await this.fetchLLM(this.modelIndex, message);
        }

        if (this.proofIndex >= this.fetchedResults[this.modelIndex].length) {
            this.modelIndex += 1;
            this.proofIndex = 0;
            return this.next(...args);
        }

        const proof = this.fetchedResults[this.modelIndex][this.proofIndex];

        this.proofIndex += 1;

        return { done: false, value: this.postProcessProof(proof) };
    }

    private async fetchLLM(index: number, message: string): Promise<ProofBatch> {
        this.progressBar.initialize(100, "id");

        let llmResponse: any = null;
        
        await this.models[index].sendMessageWithoutHistoryChange(
            message,
            this.config.config.proofAttemsPerOneTheorem
        ).then((response) => {
            logger.info("Response received: " + JSON.stringify(response));
            llmResponse = response;
        }).catch((e) => {
            logger.info("Error while generation occured: " + e.message);
            this.progressBar.finish();

            llmResponse = e;
        });

        this.progressBar.finish();

        if (llmResponse instanceof Error) {
            throw llmResponse;
        } else {
            return llmResponse;
        } 
    }
}