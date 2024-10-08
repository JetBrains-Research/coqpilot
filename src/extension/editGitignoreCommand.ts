import { appendFile, existsSync, readFileSync } from "fs";
import * as path from "path";
import { window, workspace } from "vscode";

import { showMessageToUser } from "./editorMessages";

export async function suggestAddingAuxFilesToGitignore() {
    const workspaceFolders = workspace.workspaceFolders;
    if (!workspaceFolders) {
        return;
    }

    for (const folder of workspaceFolders) {
        const gitIgnorePath = path.join(folder.uri.fsPath, ".gitignore");
        if (!existsSync(gitIgnorePath)) {
            // .gitignore not found. Exit.
            return;
        }

        const data = readFileSync(gitIgnorePath, "utf8");
        const auxExt = "*_cp_aux.v";
        if (data.indexOf(auxExt) === -1) {
            // Not found. Ask user if we should add it.
            await window
                .showInformationMessage(
                    'Do you want to add "*_cp_aux.v" to .gitignore?',
                    "Yes",
                    "No"
                )
                .then((choice) => {
                    if (choice === "Yes") {
                        const rule = `\n# CoqPilot auxiliary files\n${auxExt}`;
                        appendFile(gitIgnorePath, rule, (err) => {
                            if (err) {
                                showMessageToUser(
                                    `Unexpected error writing to .gitignore: ${err.message}`,
                                    "error"
                                );
                            } else {
                                showMessageToUser(
                                    'Successfully added "*_cp_aux.v" to .gitignore',
                                    "info"
                                );
                            }
                        });
                    }
                });
        } else {
            return;
        }
    }
}
