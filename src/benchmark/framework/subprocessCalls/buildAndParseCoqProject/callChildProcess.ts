import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { ParseCoqProjectInternalSignature } from "../../parseDataset/coqProjectParser/implementation/internalSignature";
import { ParsedWorkspaceHolder } from "../../parseDataset/coqProjectParser/implementation/parsedWorkspaceHolder";
import {
    WorkspaceRoot,
    isStandaloneFilesRoot,
} from "../../structures/workspaceRoot";
import { AsyncScheduler } from "../../utils/asyncScheduler";
import { checkIsInsideDirectory } from "../../utils/fsUtils";
import {
    ChildProcessOptions,
    executeProcessAsFunction,
} from "../../utils/subprocessUtils/ipc/childProcessExecutor/executeChildProcess";
import { ExecutionResult } from "../../utils/subprocessUtils/ipc/childProcessExecutor/executionResult";
import { buildCommandToExecuteSubprocessInWorkspace } from "../../utils/subprocessUtils/subprocessExecutionCommandBuilder";

import Signature = ParseCoqProjectInternalSignature;

export async function buildAndParseCoqProjectInSubprocess(
    workspaceRoot: WorkspaceRoot,
    workspaceTargets: Signature.ArgsModels.FilePathToFileTargets,
    buildProject: boolean,
    timeoutMillis: number | undefined,
    subprocessesScheduler: AsyncScheduler,
    benchmarkingLogger: BenchmarkingLogger,
    enableProcessLifetimeDebugLogs: boolean = false
): Promise<ExecutionResult<ParsedWorkspaceHolder>> {
    const enterWorkspaceAndExecuteSubprocessCommand =
        buildCommandToExecuteSubprocessInWorkspace(
            workspaceRoot,
            Signature.subprocessName,
            workspaceRoot !== undefined &&
                workspaceRoot.requiresNixEnvironment &&
                buildProject
                ? "nix-build"
                : undefined // TODO: support building non-nix projects with make
        );

    validateRequestedFilesAreInsideWorkspace(workspaceRoot, workspaceTargets);

    const args: Signature.ArgsModels.Args = {
        workspaceRootPath: isStandaloneFilesRoot(workspaceRoot)
            ? undefined
            : workspaceRoot.directoryPath,
        workspaceTargets: workspaceTargets,
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
                Signature.ArgsModels.argsSchema,
                Signature.ResultModels.resultSchema,
                (parsedWorkspace: Signature.ResultModels.Result) =>
                    new ParsedWorkspaceHolder(parsedWorkspace),
                options,
                benchmarkingLogger,
                enableProcessLifetimeDebugLogs
            ),
        benchmarkingLogger
    );
}

function validateRequestedFilesAreInsideWorkspace(
    workspaceRoot: WorkspaceRoot,
    workspaceTargets: Signature.ArgsModels.FilePathToFileTargets
) {
    const parentDirPath = workspaceRoot.directoryPath;
    for (const filePath in workspaceTargets) {
        // Note: assuming paths are absolute and resolved
        if (!checkIsInsideDirectory(filePath, parentDirPath)) {
            throw Error(
                `Requested file ${filePath} is expected to be inside ${parentDirPath} directory`
            );
        }
    }
}
