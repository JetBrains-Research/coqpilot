import {
    CompletionContext,
    SourceFileEnvironment,
    getTextBeforePosition,
} from "../../../../core/completionGenerator";

import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import {
    WorkspaceRoot,
    isNoWorkspaceRoot,
} from "../../structures/completionGenerationTask";
import {
    ChildProcessOptions,
    executeProcessAsFunction,
} from "../../utils/subprocessUtils/ipc/childProcessExecutor/executeChildProcess";
import { ExecutionResult } from "../../utils/subprocessUtils/ipc/childProcessExecutor/executionResult";
import { buildCommandToExecuteSubprocessInWorkspace } from "../../utils/subprocessUtils/subprocessExecutionCommandBuilder";
import { SubprocessesScheduler } from "../../utils/subprocessUtils/subprocessesScheduler";

import { CheckProofsBySubprocessSignature } from "./callSignature";

import Signature = CheckProofsBySubprocessSignature;

export async function checkGeneratedProofsInSubprocess(
    preparedProofs: string[],
    completionContext: CompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    workspaceRoot: WorkspaceRoot,
    timeoutMillis: number | undefined,
    subprocessesScheduler: SubprocessesScheduler,
    benchmarkingLogger: BenchmarkingLogger,
    enableProcessLifetimeDebugLogs: boolean = false
): Promise<ExecutionResult<Signature.Result>> {
    const enterWorkspaceAndExecuteSubprocessCommand =
        buildCommandToExecuteSubprocessInWorkspace(
            workspaceRoot,
            Signature.subprocessName
        );
    const args: Signature.Args = {
        workspaceRootPath: isNoWorkspaceRoot(workspaceRoot)
            ? undefined
            : workspaceRoot.directoryPath,
        sourceFileDirPath: sourceFileEnvironment.dirPath,
        sourceFileContentPrefix: getTextBeforePosition(
            sourceFileEnvironment.fileLines,
            completionContext.prefixEndPosition
        ),
        prefixEndPosition: completionContext.prefixEndPosition,
        preparedProofs: preparedProofs,
    };
    const options: ChildProcessOptions = {
        workingDirectory:
            enterWorkspaceAndExecuteSubprocessCommand.workingDirectory,
        timeoutMillis: timeoutMillis,
    };
    return subprocessesScheduler.scheduleSubprocess(
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
