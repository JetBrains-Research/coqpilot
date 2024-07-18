import { Goal, PpString } from "../../../../coqLsp/coqLspTypes";

import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import {
    TargetType,
    WorkspaceRoot,
    isNoWorkspaceRoot,
} from "../../structures/completionGenerationTask";
import { deserializeParsedCoqFile } from "../../structures/parsedCoqFileData";
import { TheoremData, deserializeTheorem } from "../../structures/theoremData";
import { deserializeCodeElementRange } from "../../structures/utilStructures";
import { AsyncScheduler } from "../../utils/asyncScheduler";
import { checkIsInsideDirectory } from "../../utils/fsUtils";
import {
    ChildProcessOptions,
    executeProcessAsFunction,
} from "../../utils/subprocessUtils/ipc/childProcessExecutor/executeChildProcess";
import { ExecutionResult } from "../../utils/subprocessUtils/ipc/childProcessExecutor/executionResult";
import { buildCommandToExecuteSubprocessInWorkspace } from "../../utils/subprocessUtils/subprocessExecutionCommandBuilder";

import { BuildAndParseCoqProjectBySubprocessSignature } from "./callSignature";

import Signature = BuildAndParseCoqProjectBySubprocessSignature;

export async function buildAndParseCoqProjectInSubprocess(
    workspaceRoot: WorkspaceRoot,
    sourceFileTargetsToParse: Signature.ArgsModels.FilePathToFileTarget,
    buildProject: boolean,
    timeoutMillis: number | undefined,
    subprocessesScheduler: AsyncScheduler,
    benchmarkingLogger: BenchmarkingLogger,
    enableProcessLifetimeDebugLogs: boolean = false
): Promise<ExecutionResult<Signature.UnpackedResultModels.UnpackedResult>> {
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
        sourceFileTargetsToParse
    );
    const args: Signature.ArgsModels.Args = {
        workspaceRootPath: isNoWorkspaceRoot(workspaceRoot)
            ? undefined
            : workspaceRoot.directoryPath,
        sourceFilePathToTarget: sourceFileTargetsToParse,
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
                unpackParsedFileTargets,
                options,
                benchmarkingLogger,
                enableProcessLifetimeDebugLogs
            ),
        benchmarkingLogger
    );
}

function validateRequestedFilesAreInsideWorkspace(
    workspaceRoot: WorkspaceRoot,
    sourceFileTargetsToParse: Signature.ArgsModels.FilePathToFileTarget
) {
    const parentDirPath = workspaceRoot.directoryPath;
    for (const filePath in sourceFileTargetsToParse) {
        // note: assume paths are absolute and resolved
        if (!checkIsInsideDirectory(filePath, parentDirPath)) {
            throw Error(
                `requested file "${filePath}" is expected to be inside "${parentDirPath}" directory`
            );
        }
    }
}

function unpackParsedFileTargets(
    parsedFileTargets: Signature.ResultModels.Result
): Signature.UnpackedResultModels.UnpackedResult {
    const unpackedParsedFileTargets: Signature.UnpackedResultModels.UnpackedResult =
        new Map();
    for (const filePath in parsedFileTargets) {
        const parsedFileTarget = parsedFileTargets[filePath];
        const unpackedFileTarget: Signature.UnpackedResultModels.ParsedFileTarget =
            {
                parsedFile: deserializeParsedCoqFile(
                    parsedFileTarget.serializedParsedFile
                ),
                extractedTaskTargets: parsedFileTarget.extractedTaskTargets.map(
                    (taskTarget) => {
                        return {
                            targetGoalToProve: JSON.parse(
                                taskTarget.targetGoalToProve
                            ) as Goal<PpString>, // TODO: come up with better (de)serialization
                            targetPositionRange: deserializeCodeElementRange(
                                taskTarget.targetPositionRange
                            ),
                            targetType:
                                TargetType[
                                    taskTarget.targetType as keyof typeof TargetType
                                ],
                            sourceTheorem: new TheoremData(
                                deserializeTheorem(
                                    parsedFileTarget.serializedParsedFile
                                        .allFileTheorems[
                                        taskTarget.sourceTheoremIndex
                                    ]
                                )
                            ),
                            bundleIds: new Set(taskTarget.bundleIds),
                        };
                    }
                ),
            };
        unpackedParsedFileTargets.set(filePath, unpackedFileTarget);
    }
    return unpackedParsedFileTargets;
}
