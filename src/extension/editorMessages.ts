import { appendFile, existsSync, readFileSync } from "fs";
import * as path from "path";
import { window, workspace } from "vscode";

export namespace EditorMessages {
    export const timeoutExceeded =
        "The proof checking process timed out. Please try again.";
    export const noProofsForAdmit = (admitIdentifier: any) =>
        `Coqpilot failed to find a proof for the admit at line ${admitIdentifier}.`;
    export const errorOccurred = (errorMsg: string) =>
        `Coqpilot got an error: "${errorMsg}". Please make sure the environment is properly set and the plugin is configured correctly. For more information, see the README: https://github.com/JetBrains-Research/coqpilot/blob/main/README.md. If the error appears to be a bug, please report it by opening an issue on the Coqpilot GitHub repository.`;
}

export type UIMessageSeverity = "error" | "info" | "warning";

export function showMessageToUser<T extends string>(
    message: string,
    severity: UIMessageSeverity = "info",
    ...items: T[]
): Thenable<T | undefined> {
    switch (severity) {
        case "error":
            return window.showErrorMessage(message, ...items);
        case "info":
            return window.showInformationMessage(message, ...items);
        case "warning":
            return window.showWarningMessage(message, ...items);
    }
}

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
                        const rule = `\n# Coqpilot auxiliary files\n${auxExt}`;
                        appendFile(gitIgnorePath, rule, (err) => {
                            if (err) {
                                showMessageToUser(
                                    `Unexpected error writing to .gitignore: ${err.message}`,
                                    "error"
                                );
                            } else {
                                showMessageToUser(
                                    'Successfully added "*_cp_aux.v" to .gitignore'
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
