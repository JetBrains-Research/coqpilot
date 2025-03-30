import { ProofGoal } from "../coqLsp/coqLspTypes";

import { Theorem } from "../coqParser/parsedTypes";
import { CodeElementRange } from "../utils/structures/codeElementPositions";

export interface ProofGenerationContext {
    completionTarget: string;
    contextTheorems: Theorem[];

    externalPipelineContext?: ExternalPipelineProofGenerationContext;
}

export interface ExternalPipelineProofGenerationContext {
    completionTargetGoal: ProofGoal;
    completionTargetRange: CodeElementRange;

    // TODO (!): store more abstract theorem data here
    sourceTheoremName: string;
    sourceTheoremStartLine: number;

    relativeSourceFilePath: string;
    projectRootPath: string;
}
