import {
    CompletionContext,
    SourceFileEnvironment,
    getTextBeforePosition,
} from "../../../../../core/completionGenerator";

import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { getRootDir } from "../../utils/fsUtils";
import {
    ChildProcessOptions,
    CommandToExecute,
    executeProcessAsFunction,
} from "../../utils/subprocessUtils/ipc/childProcessExecutor/executeChildProcess";
import { ExecutionResult } from "../../utils/subprocessUtils/ipc/childProcessExecutor/executionResult";
import { getSubprocessExecutableSuiteName } from "../../utils/subprocessUtils/ipc/onParentProcessCallExecutor/subprocessExecutableTestWrapper";
import { SubprocessesScheduler } from "../../utils/subprocessUtils/subprocessesScheduler";

import { CheckProofsBySubprocessSignature } from "./callSignature";

import Signature = CheckProofsBySubprocessSignature;

export async function checkGeneratedProofsInSubprocess(
    preparedProofs: string[],
    completionContext: CompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    workspaceRootPath: string | undefined,
    timeoutMillis: number | undefined,
    subprocessesScheduler: SubprocessesScheduler,
    benchmarkingLogger: BenchmarkingLogger,
    enableProcessLifetimeDebugLogs: boolean = false
): Promise<ExecutionResult<Signature.Result>> {
    // TODO: design run in nix wrapper
    const cdRoot = `cd ${getRootDir()}`;
    const runSubprocessExecutableTestSuite = `npm run test-executables-unsafe -- -g="${getSubprocessExecutableSuiteName(Signature.subprocessName)}"`;
    const executeSubprocessAsTestSuite: CommandToExecute = {
        command: "nix-shell", // TODO: it might break IPC channel between two node.js processes
        args: ["--run", `'${cdRoot} && ${runSubprocessExecutableTestSuite}'`],
    };
    const args: Signature.Args = {
        workspaceRootPath: workspaceRootPath,
        sourceFileDirPath: sourceFileEnvironment.dirPath,
        sourceFileContentPrefix: getTextBeforePosition(
            sourceFileEnvironment.fileLines,
            completionContext.prefixEndPosition
        ),
        prefixEndPosition: completionContext.prefixEndPosition,
        preparedProofs: preparedProofs,
    };
    const options: ChildProcessOptions = {
        workingDirectory: workspaceRootPath,
        timeoutMillis: timeoutMillis,
    };
    return subprocessesScheduler.scheduleSubprocess(
        () =>
            executeProcessAsFunction(
                executeSubprocessAsTestSuite,
                args,
                Signature.argsSchema,
                Signature.resultSchema,
                options,
                benchmarkingLogger,
                enableProcessLifetimeDebugLogs
            ),
        benchmarkingLogger
    );
}
