import { ProofGoal } from "../coqLsp/coqLspTypes";

import { TargetType } from "../core/completionGenerationContext";

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

    sourceTheoremName: string;
    sourceTheoremStatementRange: CodeElementRange;
    sourceTheoremProofRange: CodeElementRange;

    targetType: TargetType;

    relativeSourceFilePath: string;
    projectRootPath: string;

    requiresNixEnvironment: boolean;
}
