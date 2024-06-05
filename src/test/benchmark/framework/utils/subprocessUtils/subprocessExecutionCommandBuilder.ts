import { WorkspaceRoot } from "../../structures/completionGenerationTask";
import { getRootDir } from "../fsUtils";

import { CommandToExecute } from "./ipc/childProcessExecutor/executeChildProcess";
import { getSubprocessExecutableSuiteName } from "./ipc/onParentProcessCallExecutor/subprocessExecutableTestWrapper";

export interface ExecuteSubprocessInWorkspaceCommand extends CommandToExecute {
    workingDirectory: string | undefined;
}

export function buildExecuteSubprocessInWorkspaceCommand(
    workspaceRoot: WorkspaceRoot | undefined,
    subprocessName: string
): ExecuteSubprocessInWorkspaceCommand {
    const npmArgs = [
        "run",
        "test-executables-unsafe",
        "--",
        `-g="${getSubprocessExecutableSuiteName(subprocessName)}"`,
    ];
    if (workspaceRoot === undefined || !workspaceRoot.requiresNixEnvironment) {
        return {
            command: "npm",
            args: npmArgs,
            workingDirectory: getRootDir(),
        };
    }
    const cdRoot = `cd ${getRootDir()}`;
    const runSubprocessExecutableTestSuite = `npm ${npmArgs.join(" ")}`;
    return {
        command: "nix-shell", // TODO: `nix-shell` might break IPC channel between two node.js processes...
        args: ["--run", `'${cdRoot} && ${runSubprocessExecutableTestSuite}'`],
        workingDirectory: workspaceRoot.directoryPath,
    };
}
