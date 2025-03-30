import { workspace } from "vscode";

import { Uri } from "../../utils/structures/uri";
import {
    EditorMessages,
    showMessageToUser,
} from "../ui/messages/editorMessages";

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
