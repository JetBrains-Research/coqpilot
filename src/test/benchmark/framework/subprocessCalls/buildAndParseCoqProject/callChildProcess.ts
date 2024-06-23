import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { WorkspaceRoot } from "../../structures/completionGenerationTask";
import {
    ParsedCoqFileData,
    deserializeParsedCoqFile,
} from "../../structures/parsedCoqFileData";
import { checkIsInsideDirectory, getDatasetDir } from "../../utils/fsUtils";
import {
    ChildProcessOptions,
    executeProcessAsFunction,
} from "../../utils/subprocessUtils/ipc/childProcessExecutor/executeChildProcess";
import { ExecutionResult } from "../../utils/subprocessUtils/ipc/childProcessExecutor/executionResult";
import { buildCommandToExecuteSubprocessInWorkspace } from "../../utils/subprocessUtils/subprocessExecutionCommandBuilder";
import { SubprocessesScheduler } from "../../utils/subprocessUtils/subprocessesScheduler";

import { BuildAndParseCoqProjectBySubprocessSignature } from "./callSignature";

import Signature = BuildAndParseCoqProjectBySubprocessSignature;

export async function buildAndParseCoqProjectInSubprocess(
    workspaceRoot: WorkspaceRoot | undefined,
    sourceFilesToParsePaths: string[],
    buildProject: boolean,
    timeoutMillis: number | undefined,
    subprocessesScheduler: SubprocessesScheduler,
    benchmarkingLogger: BenchmarkingLogger,
    enableProcessLifetimeDebugLogs: boolean = false
): Promise<ExecutionResult<ParsedCoqFileData[]>> {
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
    validateRequestedFilesAreInsideWorkspace(
        workspaceRoot,
        sourceFilesToParsePaths
    );
    const args: Signature.Args = {
        workspaceRootPath: workspaceRoot?.directoryPath,
        sourceFilesToParsePaths: sourceFilesToParsePaths,
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
                (serializedParsedFiles) =>
                    serializedParsedFiles.map(deserializeParsedCoqFile),
                options,
                benchmarkingLogger,
                enableProcessLifetimeDebugLogs
            ),
        benchmarkingLogger
    );
}

function validateRequestedFilesAreInsideWorkspace(
    workspaceRoot: WorkspaceRoot | undefined,
    sourceFilesToParsePaths: string[]
) {
    const parentDirPath = workspaceRoot?.directoryPath ?? getDatasetDir();
    for (const filePath of sourceFilesToParsePaths) {
        // note: assume paths are absolute and resolved
        if (!checkIsInsideDirectory(filePath, parentDirPath)) {
            throw Error(
                `requested file "${filePath}" is expected to be inside "${parentDirPath}" directory`
            );
        }
    }
}
