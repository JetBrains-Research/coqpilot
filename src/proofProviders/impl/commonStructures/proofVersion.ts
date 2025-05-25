import { GeneratedRawContentItem } from "./generatedRawContent";

export interface ProofVersion {
    proof: string;
    rawProof: GeneratedRawContentItem;
    diagnostic?: string;
}
