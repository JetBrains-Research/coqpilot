import { workspace } from "vscode";

import { ProjectRoot } from "../../utils/structures/projectRoot";
import { Uri } from "../../utils/structures/uri";
import {
    EditorMessages,
    showMessageToUser,
} from "../ui/messages/editorMessages";

/**
 * Use this function only to retrieve a default value, which can be reconfigured manually later.
 * Both `projectRoot.uri` and `projectRoot.requiresNixEnvironment` might not be accurate.
 */
export function inferProjectRoot(): ProjectRoot | undefined {
    const projectRootUri = getOpenedWorkspaceAsProjectRoot();
    if (projectRootUri === undefined) {
        return undefined;
    }
    return {
        uri: projectRootUri,
        requiresNixEnvironment: isRunningInNixEnvironment(),
    };
}

/**
 * _Warning:_ we assume that the project root is similar to the opened VS Code workspace;
 * however, that might not be true.
 *
 * Use this function only to retrieve a default value, which can be reconfigured manually later.
 */
export function getOpenedWorkspaceAsProjectRoot(): Uri | undefined {
    const openedWorkspaces = workspace.workspaceFolders;
    if (openedWorkspaces === undefined) {
        showMessageToUser(EditorMessages.noWorkspaceIsOpened, "warning");
        return undefined;
    }
    const targetWorkspace = Uri.fromPath(openedWorkspaces[0].uri.fsPath);
    if (openedWorkspaces.length > 1) {
        showMessageToUser(
            EditorMessages.multipleWorkspacesAreOpened,
            "warning"
        );
        return undefined;
    }
    return targetWorkspace;
}

export function isRunningInNixEnvironment(): boolean {
    const env = process.env;
    return (
        env.IN_NIX_SHELL !== undefined ||
        env.NIX_PROFILES !== undefined ||
        env.NIX_PATH !== undefined
    );
}
