import {
    WorkspaceRoot,
    isNoWorkspaceRoot,
} from "../../structures/completionGenerationTask";
import { getRootDir } from "../fsUtils";

import { CommandToExecute } from "./ipc/childProcessExecutor/executeChildProcess";
import { getSubprocessExecutableSuiteName } from "./ipc/onParentProcessCallExecutor/subprocessExecutableTestWrapper";

export interface ExecuteSubprocessInWorkspaceCommand extends CommandToExecute {
    workingDirectory: string | undefined;
}

export function buildCommandToExecuteSubprocessInWorkspace(
    workspaceRoot: WorkspaceRoot,
    subprocessName: string,
    commandToPrepareWorkspace?: string
): ExecuteSubprocessInWorkspaceCommand {
    const npmArgs = [
        "run",
        "test-executables-unsafe",
        "--",
        `-g="${getSubprocessExecutableSuiteName(subprocessName)}"`,
    ];
    if (
        isNoWorkspaceRoot(workspaceRoot) ||
        !workspaceRoot.requiresNixEnvironment
    ) {
        // TODO: support workspace preparation if workspaceRoot is set but does not require nix
        return {
            command: "npm",
            args: npmArgs,
            workingDirectory: getRootDir(),
        };
    }
    const prepareWorkspace =
        commandToPrepareWorkspace === undefined
            ? ""
            : `${commandToPrepareWorkspace} && `;
    const cdRoot = `cd ${getRootDir()}`;
    const runSubprocessExecutableTestSuite = `npm ${npmArgs.join(" ")}`;
    return {
        command: "nix-shell", // TODO: `nix-shell` might break IPC channel between two node.js processes...
        args: [
            "--run",
            `'${prepareWorkspace}${cdRoot} && ${runSubprocessExecutableTestSuite}'`,
        ],
        workingDirectory: workspaceRoot.directoryPath,
    };
}
