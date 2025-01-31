import {
    AbstractProofsChecker,
    ProofsCheckArgs,
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
        inputArgs: ProofsCheckArgs
    ): Promise<ProofsCheckResult> {
        const args = ProofsCheckerUtils.buildArgs(preparedProofs, inputArgs);
        const proofsCheckResult = await CheckProofsImpl.checkProofsMeasured(
            args,
            undefined,
            inputArgs.abortSignal
        );
        return ProofsCheckerUtils.unpackSuccessResultOrThrow(proofsCheckResult);
    }
}
