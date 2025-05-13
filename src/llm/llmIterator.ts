import { EventLogger } from "../logging/eventLogger";

import { ResolvedGenerationBundles } from "./generationBundles";
import { GeneratedProof } from "./llmServices/generatedProof";
import { LLMService } from "./llmServices/llmService";
import { LLMServiceIdentifier } from "./llmServices/llmServiceIdentifier";
import { ModelParams } from "./llmServices/modelParams";
import { ProofGenerationContext } from "./proofGenerationContext";

type GeneratedProofsBatch = GeneratedProof[];
type ProofsGenerationHook = () => Promise<GeneratedProofsBatch>;

export const DEFAULT_FETCHING_ORDER = [
    LLMServiceIdentifier.PREDEFINED_PROOFS,
    // Here DeepSeek service is reordered to the beginning
    // of the list, due to it's strong performance and
    // low costs. Refer to discussion:
    // https://github.com/JetBrains-Research/coqpilot/pull/56#discussion_r1935180516
    LLMServiceIdentifier.DEEPSEEK,
    LLMServiceIdentifier.OPENAI,
    LLMServiceIdentifier.GRAZIE,
    LLMServiceIdentifier.LMSTUDIO,
    LLMServiceIdentifier.RANGO,
];

export class LLMSequentialIterator
    implements AsyncIterator<GeneratedProofsBatch>
{
    private proofsGenerationHook: ProofsGenerationHook[];
    private fetchedResults: GeneratedProofsBatch[];

    private hooksIndex: number;
    private insideBatchIndex: number;

    constructor(
        proofGenerationContext: ProofGenerationContext,
        bundles: ResolvedGenerationBundles,
        servicesToFetchInOrder: LLMServiceIdentifier[] = DEFAULT_FETCHING_ORDER,
        private readonly eventLogger?: EventLogger,
        private readonly abortSignal?: AbortSignal
    ) {
        this.hooksIndex = 0;
        this.insideBatchIndex = 0;
        this.proofsGenerationHook = this.createHooks(
            proofGenerationContext,
            servicesToFetchInOrder,
            bundles
        );
        this.fetchedResults = new Array<GeneratedProofsBatch>(
            this.proofsGenerationHook.length
        );
    }

    private createHooks(
        proofGenerationContext: ProofGenerationContext,
        servicesToFetchInOrder: LLMServiceIdentifier[],
        bundles: ResolvedGenerationBundles
    ): ProofsGenerationHook[] {
        const hooks: ProofsGenerationHook[][] = [];
        for (const identifier of servicesToFetchInOrder) {
            const serviceToFetchBundles = bundles.getBundles(identifier);
            for (const bundle of serviceToFetchBundles) {
                hooks.push(
                    this.createLLMServiceHooks(
                        proofGenerationContext,
                        bundle.models,
                        bundle.llmService
                    )
                );
            }
        }
        return hooks.flat();
    }

    private createLLMServiceHooks<ResolvedModelParams extends ModelParams>(
        proofGenerationContext: ProofGenerationContext,
        allModelParamsForService: ResolvedModelParams[],
        llmService: LLMService<any, ResolvedModelParams>
    ): ProofsGenerationHook[] {
        const serviceLoggingName =
            LLMSequentialIterator.getServiceLoggingName(llmService);
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
                    modelParams,
                    undefined,
                    undefined,
                    this.abortSignal
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

    private static getServiceLoggingName(llmService: LLMService): string {
        const fullName = llmService.name;
        return fullName
            .replace(/Service$/, "")
            .replace(/([a-z])([A-Z])/g, "$1-$2")
            .toLowerCase();
    }
}
