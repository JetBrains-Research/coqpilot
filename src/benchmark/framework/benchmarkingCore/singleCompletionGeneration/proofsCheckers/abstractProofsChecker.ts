import {
    CompletionContext,
    SourceFileEnvironment,
} from "../../../../../core/completionGenerationContext";
import { ProofCheckResult } from "../../../../../core/coqProofChecker";

import { BenchmarkingLogger } from "../../../logging/benchmarkingLogger";
import { WorkspaceRoot } from "../../../structures/common/workspaceRoot";

export interface ProofsCheckResult {
    checkedProofs: ProofCheckResult[];
    proofCheckElapsedMillis: number;
    totalEffectiveElapsedMillis: number;
}

export type ProofsCheckFailureType =
    | "COQ_LSP_TIMEOUT"
    | "COQ_PROOF_CHECKER_ERROR";

export class ProofsCheckFailedError extends Error {
    constructor(
        readonly failureType: ProofsCheckFailureType,
        readonly causeMessage: string
    ) {
        super(causeMessage);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "ProofsCheckFailedError";
    }
}

export abstract class AbstractProofsChecker {
    abstract checkProofs(
        preparedProofs: string[],
        completionContext: CompletionContext,
        sourceFileEnvironment: SourceFileEnvironment,
        workspaceRoot: WorkspaceRoot,
        timeoutMillis: number | undefined,
        logger: BenchmarkingLogger,
        abortSignal: AbortSignal
    ): Promise<ProofsCheckResult>;
}
