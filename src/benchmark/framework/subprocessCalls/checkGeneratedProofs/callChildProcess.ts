import {
    CompletionContext,
    SourceFileEnvironment,
} from "../../../../core/completionGenerationContext";

import { CheckProofsInternalSignature } from "../../benchmarkCompletionGeneration/proofsCheckers/implementation/internalSignature";
import { ProofsCheckerUtils } from "../../benchmarkCompletionGeneration/proofsCheckers/implementation/proofsCheckerUtils";
import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { WorkspaceRoot } from "../../structures/common/workspaceRoot";
import { AsyncScheduler } from "../../utils/asyncScheduler";
import {
    ChildProcessOptions,
    executeProcessAsFunction,
} from "../../utils/subprocessUtils/ipc/childProcessExecutor/executeChildProcess";
import { ExecutionResult } from "../../utils/subprocessUtils/ipc/childProcessExecutor/executionResult";
import { buildCommandToExecuteSubprocessInWorkspace } from "../../utils/subprocessUtils/subprocessExecutionCommandBuilder";

import Signature = CheckProofsInternalSignature;

export async function checkGeneratedProofsInSubprocess(
    preparedProofs: string[],
    completionContext: CompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    workspaceRoot: WorkspaceRoot,
    timeoutMillis: number | undefined,
    subprocessesScheduler: AsyncScheduler,
    benchmarkingLogger: BenchmarkingLogger,
    enableProcessLifetimeDebugLogs: boolean = false
): Promise<ExecutionResult<Signature.Result>> {
    const enterWorkspaceAndExecuteSubprocessCommand =
        buildCommandToExecuteSubprocessInWorkspace(
            workspaceRoot,
            Signature.subprocessName
        );
    const args = ProofsCheckerUtils.buildArgs(
        preparedProofs,
        completionContext,
        sourceFileEnvironment,
        workspaceRoot
    );
    const options: ChildProcessOptions = {
        workingDirectory:
            enterWorkspaceAndExecuteSubprocessCommand.workingDirectory,
        timeoutMillis: timeoutMillis,
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
                benchmarkingLogger,
                enableProcessLifetimeDebugLogs
            ),
        benchmarkingLogger
    );
}
