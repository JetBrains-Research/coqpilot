import { AsyncScheduler } from "../../../../../utils/async/asyncScheduler";
import { throwError } from "../../../../../utils/errors/throwErrors";
import { checkGeneratedProofsInSubprocess } from "../../../subprocessCalls/checkGeneratedProofs/callChildProcess";

import {
    AbstractProofsChecker,
    ProofsCheckArgs,
    ProofsCheckResult,
} from "./abstractProofsChecker";
import { ProofsCheckerUtils } from "./implementation/proofsCheckerUtils";

export class SubprocessProofsChecker extends AbstractProofsChecker {
    constructor(
        private readonly subprocessesScheduler: AsyncScheduler,
        private readonly checkProofsSubprocessTimeoutMillis: number | undefined,
        private readonly enableSubprocessLifetimeDebugLogs: boolean
    ) {
        super();
    }

    async checkProofs(
        preparedProofs: string[],
        inputArgs: ProofsCheckArgs
    ): Promise<ProofsCheckResult> {
        const proofsCheckExecutionResult =
            await checkGeneratedProofsInSubprocess(
                preparedProofs,
                inputArgs,
                this.checkProofsSubprocessTimeoutMillis,
                this.subprocessesScheduler,
                this.enableSubprocessLifetimeDebugLogs
            );
        if (proofsCheckExecutionResult.isFailed()) {
            // TODO: this throw should be revised
            throwError(proofsCheckExecutionResult.errorMessage);
        }
        return ProofsCheckerUtils.unpackSuccessResultOrThrow(
            proofsCheckExecutionResult.maybeResult!
        );
    }
}
