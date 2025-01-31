import { ProofsCheckArgs } from "../../benchmarkingCore/singleCompletionGeneration/proofsCheckers/abstractProofsChecker";
import { CheckProofsInternalSignature } from "../../benchmarkingCore/singleCompletionGeneration/proofsCheckers/implementation/internalSignature";
import { ProofsCheckerUtils } from "../../benchmarkingCore/singleCompletionGeneration/proofsCheckers/implementation/proofsCheckerUtils";
import { AsyncScheduler } from "../../utils/asyncUtils/asyncScheduler";
import {
    ChildProcessOptions,
    executeProcessAsFunction,
} from "../../utils/subprocessUtils/ipc/childProcessExecutor/executeChildProcess";
import { ExecutionResult } from "../../utils/subprocessUtils/ipc/childProcessExecutor/executionResult";
import { buildCommandToExecuteSubprocessInWorkspace } from "../../utils/subprocessUtils/subprocessExecutionCommandBuilder";

import Signature = CheckProofsInternalSignature;

export async function checkGeneratedProofsInSubprocess(
    preparedProofs: string[],
    inputArgs: ProofsCheckArgs,
    subprocessTimeoutMillis: number | undefined,
    subprocessesScheduler: AsyncScheduler,
    enableProcessLifetimeDebugLogs: boolean = false
): Promise<ExecutionResult<Signature.Result>> {
    const enterWorkspaceAndExecuteSubprocessCommand =
        buildCommandToExecuteSubprocessInWorkspace(
            inputArgs.workspaceRoot,
            Signature.subprocessName
        );
    const args = ProofsCheckerUtils.buildArgs(preparedProofs, inputArgs);
    const options: ChildProcessOptions = {
        workingDirectory:
            enterWorkspaceAndExecuteSubprocessCommand.workingDirectory,
        timeoutMillis: subprocessTimeoutMillis,
    };
    return subprocessesScheduler.scheduleTask(
        () =>
            executeProcessAsFunction(
                enterWorkspaceAndExecuteSubprocessCommand,
                args,
                Signature.argsSchema,
                Signature.resultSchema,
                (result) => result,
                options,
                inputArgs.logger,
                enableProcessLifetimeDebugLogs
            ),
        inputArgs.logger
    );
}
