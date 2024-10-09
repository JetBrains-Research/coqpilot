import {
    CompletionContext,
    SourceFileEnvironment,
} from "../../../../../core/completionGenerationContext";
import { ProofCheckResult } from "../../../../../core/coqProofChecker";

import { BenchmarkingLogger } from "../../../logging/benchmarkingLogger";
import { WorkspaceRoot } from "../../../structures/common/workspaceRoot";

export interface ProofsCheckResult {
    checkedProofs: ProofCheckResult[];
    effectiveElapsedMillis: number;
}

export type ProofsCheckFailureType = "TIMEOUT" | "COQ_PROOF_CHECKER_ERROR";

export class ProofsCheckFailedError extends Error {
    constructor(
        readonly failureType: ProofsCheckFailureType,
        readonly causeMessage: string
    ) {
        super(causeMessage);
    }
}

export abstract class AbstractProofsChecker {
    abstract checkProofs(
        preparedProofs: string[],
        completionContext: CompletionContext,
        sourceFileEnvironment: SourceFileEnvironment,
        workspaceRoot: WorkspaceRoot,
        logger: BenchmarkingLogger
    ): Promise<ProofsCheckResult>;
}