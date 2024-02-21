import { ProofGenerationContext, ModelParams } from "./modelParamsInterfaces";

export type LlmServiceId = string;

export interface LLMServiceInterface {
    generateProof(
        proofGenerationContext: ProofGenerationContext,
        params: ModelParams
    ): Promise<string[]>;

    dispose(): void;
}
