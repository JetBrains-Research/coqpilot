import {
    CompletionContext,
    SourceFileEnvironment,
} from "../../../../core/completionGenerationContext";
import { getTextBeforePosition } from "../../../../core/exposedCompletionGeneratorUtils";

import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import {
    WorkspaceRoot,
    isStandaloneFilesRoot,
} from "../../structures/workspaceRoot";
import { AsyncScheduler } from "../../utils/asyncScheduler";
import {
    ChildProcessOptions,
    executeProcessAsFunction,
} from "../../utils/subprocessUtils/ipc/childProcessExecutor/executeChildProcess";
import { ExecutionResult } from "../../utils/subprocessUtils/ipc/childProcessExecutor/executionResult";
import { buildCommandToExecuteSubprocessInWorkspace } from "../../utils/subprocessUtils/subprocessExecutionCommandBuilder";

import { CheckProofsBySubprocessSignature } from "./callSignature";

import Signature = CheckProofsBySubprocessSignature;

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
    const args: Signature.Args = {
        workspaceRootPath: isStandaloneFilesRoot(workspaceRoot)
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
