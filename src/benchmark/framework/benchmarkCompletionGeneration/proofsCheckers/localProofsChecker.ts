import {
    CompletionContext,
    SourceFileEnvironment,
} from "../../../../core/completionGenerationContext";

import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { WorkspaceRoot } from "../../structures/workspaceRoot";

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
        logger: BenchmarkingLogger
    ): Promise<ProofsCheckResult> {
        const args = ProofsCheckerUtils.buildArgs(
            preparedProofs,
            completionContext,
            sourceFileEnvironment,
            workspaceRoot
        );
        const proofsCheckResult = await CheckProofsImpl.checkProofsMeasured(
            args,
            logger
        );
        return ProofsCheckerUtils.unpackSuccessResultOrThrow(proofsCheckResult);
    }
}
