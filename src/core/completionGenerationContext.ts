import { Range } from "vscode-languageclient";

import { LLMServices } from "../llm/llmServices";
import { ModelsParams } from "../llm/llmServices/modelParams";

import { ProofGoal } from "../coqLsp/coqLspTypes";

import { Theorem } from "../coqParser/parsedTypes";
import { ProjectRoot } from "../utils/structures/projectRoot";
import { Uri } from "../utils/structures/uri";

import { ContextTheoremsRanker } from "./contextTheoremRanker/contextTheoremsRanker";
import { CoqProofChecker } from "./coqProofChecker";

export interface CompletionContext {
    proofGoal: ProofGoal;
    admitRange: Range;
    sourceTheorem: Theorem;
}

export interface SourceFileEnvironment {
    /**
     * Contains only ones that successfully finish with `Qed`.
     */
    fileTheorems: Theorem[];
    documentVersion: number;
    fileUri: Uri;

    /**
     * This value is optional, most of the functionality does not require it to be defined.
     *
     * However, it is not true for some modules: currently, it is needed to build the `ExternalPipelineProofGenerationContext`
     * inside the `ProofGenerationContext` that is used by some external proof generators (such as Rango).
     *
     * _Conclusion:_ define this value whether it is possible, this way all the functionality will be available.
     */
    projectRoot?: ProjectRoot;
}

export interface ProcessEnvironment {
    coqProofChecker: CoqProofChecker;
    modelsParams: ModelsParams;
    services: LLMServices;
    /**
     * If `theoremRanker` is not provided, the default one will be used:
     * theorems would be passed sequentially in the same order as they are in the file
     */
    theoremRanker?: ContextTheoremsRanker;
    premisesNumber?: number;
}
