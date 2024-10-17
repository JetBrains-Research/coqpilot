import { Range } from "vscode-languageclient";

import { LLMServices } from "../llm/llmServices";
import { ModelsParams } from "../llm/llmServices/modelParams";

import { ProofGoal } from "../coqLsp/coqLspTypes";

import { Theorem } from "../coqParser/parsedTypes";
import { Uri } from "../utils/uri";

import { ContextTheoremsRanker } from "./contextTheoremRanker/contextTheoremsRanker";
import { CoqProofChecker } from "./coqProofChecker";

export interface CompletionContext {
    proofGoal: ProofGoal;
    admitRange: Range;
}

export interface SourceFileEnvironment {
    // `fileTheorems` contain only ones that successfully finish with Qed.
    fileTheorems: Theorem[];
    // TODO: [LspCoreRefactor] Check if `fileLines` is needed
    fileLines: string[];
    // TODO: [LspCoreRefactor] Check if `fileVersion` is provided correctly && rename to `documentVersion`
    fileVersion: number;
    // TODO: [LspCoreRefactor] Remove `dirPath` from here as it is probably not used anymore
    dirPath: string;
    // TODO: [LspCoreRefactor] Rename to `documentUri`
    fileUri: Uri;
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
