import { ResolvedGenerationBundles } from "../proofProviders/generationBundles";
import { GeneratedProof } from "../proofProviders/impl/generatedProof";
import { ModelParams } from "../proofProviders/impl/modelParams";
import { ProofProvider } from "../proofProviders/impl/proofProvider";
import { ProofProviderIdentifier } from "../proofProviders/impl/proofProviderIdentifier";
import { ProofGenerationContext } from "../proofProviders/proofGenerationContext";

import { EventLogger } from "../logging/eventLogger";

type GeneratedProofsBatch = GeneratedProof[];
type ProofsGenerationHook = () => Promise<GeneratedProofsBatch>;

export const DEFAULT_FETCHING_ORDER = [
    ProofProviderIdentifier.PREDEFINED_PROOFS,
    // Here DeepSeek proofProvider is reordered to the beginning
    // of the list, due to it's strong performance and
    // low costs. Refer to discussion:
    // https://github.com/JetBrains-Research/coqpilot/pull/56#discussion_r1935180516
    ProofProviderIdentifier.DEEPSEEK,
    ProofProviderIdentifier.OPENAI,
    ProofProviderIdentifier.GRAZIE,
    ProofProviderIdentifier.LMSTUDIO,
    ProofProviderIdentifier.RANGO,
];

export class ModelsSequentialIterator
    implements AsyncIterator<GeneratedProofsBatch>
{
    private proofsGenerationHook: ProofsGenerationHook[];
    private fetchedResults: GeneratedProofsBatch[];

    private hooksIndex: number;
    private insideBatchIndex: number;

    constructor(
        proofGenerationContext: ProofGenerationContext,
        bundles: ResolvedGenerationBundles,
        proofProvidersToFetchInOrder: ProofProviderIdentifier[] = DEFAULT_FETCHING_ORDER,
        private readonly eventLogger?: EventLogger,
        private readonly abortSignal?: AbortSignal
    ) {
        this.hooksIndex = 0;
        this.insideBatchIndex = 0;
        this.proofsGenerationHook = this.createHooks(
            proofGenerationContext,
            proofProvidersToFetchInOrder,
            bundles
        );
        this.fetchedResults = new Array<GeneratedProofsBatch>(
            this.proofsGenerationHook.length
        );
    }

    private createHooks(
        proofGenerationContext: ProofGenerationContext,
        proofProvidersToFetchInOrder: ProofProviderIdentifier[],
        bundles: ResolvedGenerationBundles
    ): ProofsGenerationHook[] {
        const hooks: ProofsGenerationHook[][] = [];
        for (const identifier of proofProvidersToFetchInOrder) {
            const proofProviderToFetchBundles = bundles.getBundles(identifier);
            for (const bundle of proofProviderToFetchBundles) {
                hooks.push(
                    this.createProofProviderHooks(
                        proofGenerationContext,
                        bundle.models,
                        bundle.proofProvider
                    )
                );
            }
        }
        return hooks.flat();
    }

    private createProofProviderHooks<ResolvedModelParams extends ModelParams>(
        proofGenerationContext: ProofGenerationContext,
        allModelParamsForProofProvider: ResolvedModelParams[],
        proofProvider: ProofProvider<any, ResolvedModelParams>
    ): ProofsGenerationHook[] {
        const proofProviderLoggingName =
            ModelsSequentialIterator.getProofProviderLoggingName(proofProvider);
        const hooks = [];
        for (const modelParams of allModelParamsForProofProvider) {
            hooks.push(() => {
                this.eventLogger?.log(
                    `${proofProviderLoggingName}-fetch-started`,
                    `Completion from ${proofProviderLoggingName}`,
                    modelParams
                );
                return proofProvider.generateProof(
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

    private static getProofProviderLoggingName(
        proofProvider: ProofProvider
    ): string {
        const fullName = proofProvider.name;
        return fullName
            .replace(/Service$/, "")
            .replace(/([a-z])([A-Z])/g, "$1-$2")
            .toLowerCase();
    }
}
