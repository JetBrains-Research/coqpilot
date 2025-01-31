import {
    CompletionContext,
    SourceFileEnvironment,
} from "../../../../../core/completionGenerationContext";

import { BenchmarkingLogger } from "../../../logging/benchmarkingLogger";
import { WorkspaceRoot } from "../../../structures/common/workspaceRoot";

import {
    AbstractProofsChecker,
    ProofsCheckResult,
} from "./abstractProofsChecker";
import { CheckProofsImpl } from "./implementation/checkProofs";
import { ProofsCheckerUtils } from "./implementation/proofsCheckerUtils";

/**
 * **Warning:** This implementation requires the `vscode` module to function.
 * It should not be used in code executed outside the `test-electron` environment.
 */
export class LocalProofsChecker extends AbstractProofsChecker {
    async checkProofs(
        preparedProofs: string[],
        completionContext: CompletionContext,
        sourceFileEnvironment: SourceFileEnvironment,
        workspaceRoot: WorkspaceRoot,
        proofCheckTimeoutMillis: number | undefined,
        _logger: BenchmarkingLogger,
        abortSignal: AbortSignal
    ): Promise<ProofsCheckResult> {
        const args = ProofsCheckerUtils.buildArgs(
            preparedProofs,
            completionContext,
            sourceFileEnvironment,
            workspaceRoot,
            proofCheckTimeoutMillis
        );
        const proofsCheckResult = await CheckProofsImpl.checkProofsMeasured(
            args,
            undefined,
            abortSignal
        );
        return ProofsCheckerUtils.unpackSuccessResultOrThrow(proofsCheckResult);
    }
}
