import { Goal, PpString } from "../../../../../coqLsp/coqLspTypes";

import { FilePathToFileTarget } from "../../experiment/targetsBuilder";
import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import {
    TargetType,
    WorkspaceRoot,
} from "../../structures/completionGenerationTask";
import { deserializeParsedCoqFile } from "../../structures/parsedCoqFileData";
import { TheoremData, deserializeTheorem } from "../../structures/theoremData";
import { deserializeCodeElementRange } from "../../structures/utilStructures";
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
    sourceFileTargetsToParse: FilePathToFileTarget,
    buildProject: boolean,
    timeoutMillis: number | undefined,
    subprocessesScheduler: SubprocessesScheduler,
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
        Array.from(sourceFileTargetsToParse.keys())
    );
    const args: Signature.ArgsModels.Args = {
        workspaceRootPath: workspaceRoot?.directoryPath,
        sourceFilePathToTarget: packFileTargetsIntoArgs(
            sourceFileTargetsToParse
        ),
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
    workspaceRoot: WorkspaceRoot | undefined,
    sourceFilesPaths: string[]
) {
    const parentDirPath = workspaceRoot?.directoryPath ?? getDatasetDir();
    for (const filePath of sourceFilesPaths) {
        // note: assume paths are absolute and resolved
        if (!checkIsInsideDirectory(filePath, parentDirPath)) {
            throw Error(
                `requested file "${filePath}" is expected to be inside "${parentDirPath}" directory`
            );
        }
    }
}

function packFileTargetsIntoArgs(
    sourceFileTargetsToParse: FilePathToFileTarget
): Signature.ArgsModels.FilePathToFileTarget {
    const packedFileTargets: Signature.ArgsModels.FilePathToFileTarget = {};
    for (const [filePath, fileTarget] of sourceFileTargetsToParse.entries()) {
        const packedFileTarget: Signature.ArgsModels.FileTarget = {
            specificTheoremTargets: {},
            allTheoremsTargetTypes: [],
        };
        if (fileTarget.allTheoremsAsAdmitTargets) {
            packedFileTarget.allTheoremsTargetTypes.push("ADMIT");
        }
        if (fileTarget.allTheoremsAsProveTheoremTargets) {
            packedFileTarget.allTheoremsTargetTypes.push("PROVE_THEOREM");
        }
        for (const [
            theoremName,
            theoremTarget,
        ] of fileTarget.specificTheoremTargets.entries()) {
            const packedTheoremTarget: Signature.ArgsModels.TheoremTarget = {
                targetTypes: [],
            };
            if (
                theoremTarget.admitTargets &&
                !fileTarget.allTheoremsAsAdmitTargets
            ) {
                packedTheoremTarget.targetTypes.push("ADMIT");
            }
            if (
                theoremTarget.proveTheoremTarget &&
                !fileTarget.allTheoremsAsProveTheoremTargets
            ) {
                packedTheoremTarget.targetTypes.push("PROVE_THEOREM");
            }
            if (packedTheoremTarget.targetTypes.length === 0) {
                continue;
            }
            packedFileTarget.specificTheoremTargets[theoremName] =
                packedTheoremTarget;
        }
        packedFileTargets[filePath] = packedFileTarget;
    }
    return packedFileTargets;
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
                        };
                    }
                ),
            };
        unpackedParsedFileTargets.set(filePath, unpackedFileTarget);
    }
    return unpackedParsedFileTargets;
}
