import { Position } from "vscode-languageclient";

import { LLMServices } from "../llm/llmServices";
import { ModelsParams } from "../llm/llmServices/modelParams";

import { ProofGoal } from "../coqLsp/coqLspTypes";

import { Theorem } from "../coqParser/parsedTypes";

import { ContextTheoremsRanker } from "./contextTheoremRanker/contextTheoremsRanker";
import { CoqProofChecker } from "./coqProofChecker";

export interface CompletionContext {
    proofGoal: ProofGoal;
    prefixEndPosition: Position;
    admitEndPosition: Position;
}

export interface SourceFileEnvironment {
    // `fileTheorems` contain only ones that successfully finish with Qed.
    fileTheorems: Theorem[];
    fileLines: string[];
    fileVersion: number;
    dirPath: string;
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
