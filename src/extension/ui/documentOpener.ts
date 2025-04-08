import { Uri, window, workspace } from "vscode";

import { getErrorMessage } from "../../utils/errors/errorsUtils";
import { exists } from "../../utils/fs/pathUtils";

import { showMessageToUser } from "./messages/editorMessages";

export async function openTextDocument(filePath: string) {
    if (exists(filePath)) {
        await workspace.openTextDocument(Uri.file(filePath)).then(
            (doc) => window.showTextDocument(doc),
            (err) =>
                showMessageToUser(
                    `Failed to open file ${filePath}: ${getErrorMessage(err)}`,
                    "error"
                )
        );
    } else {
        showMessageToUser(`The file does not exist: ${filePath}`, "error");
    }
}
