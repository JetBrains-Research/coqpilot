import { illegalState } from "../../../../utils/throwErrors";
import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { CoqProjectParserUtils } from "../../parseDataset/coqProjectParser/implementation/coqProjectParserUtils";
import { ParseCoqProjectInternalSignature } from "../../parseDataset/coqProjectParser/implementation/internalSignature";
import { ParsedWorkspaceHolder } from "../../parseDataset/coqProjectParser/implementation/parsedWorkspaceHolder";
import { WorkspaceRoot } from "../../structures/common/workspaceRoot";
import { AsyncScheduler } from "../../utils/asyncUtils/asyncScheduler";
import { checkIsInsideDirectory } from "../../utils/fileUtils/fs";
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
    openDocumentTimeoutMillis: number | undefined,
    buildProject: boolean,
    subprocessTimeoutMillis: number | undefined,
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

    const args = CoqProjectParserUtils.buildArgs(
        workspaceTargets,
        workspaceRoot,
        openDocumentTimeoutMillis
    );
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
            illegalState(
                `Requested file ${filePath} is expected to be inside ${parentDirPath} directory`
            );
        }
    }
}
