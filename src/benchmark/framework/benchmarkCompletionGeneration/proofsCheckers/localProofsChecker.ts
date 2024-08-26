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
 * **Warning:** this part of implementation requires `vscode` module imported to work.
 * Thus, do not use it in the code that is called outside the `test-electron` environment.
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
