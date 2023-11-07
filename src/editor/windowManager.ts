import * as vscode from 'vscode';
import * as glob from 'glob';
import * as path from 'path';
import * as fs from 'fs';

import logger from '../extension/logger';

export function showApiKeyNotProvidedMessage() {
    vscode.window.showInformationMessage(
        'Please set your OpenAI API key in the settings.', 
        'Open settings'
    ).then((value) => {
        if (value === 'Open settings') {
            vscode.commands.executeCommand('workbench.action.openSettings', 'coqpilot.openaiApiKey');
        }
    });
}

export function showParsingFinishedMessage() {
    vscode.window.showInformationMessage(
        'File analysis finished successfully.'
    );
}

export function showIncorrectFileFormatMessage() {
    vscode.window.showInformationMessage(
        'Please open a Coq file first.'
    );
}

export function noTheoremInSelectionMessage() {
    vscode.window.showInformationMessage(
        'Please select a theorem to prove. Select it by highlighting the whole theorem, including the Admitted.'
    );
}

export function showSearchFailureMessage(theoremName: string) {
    vscode.window.showInformationMessage(
        'Coqpilot failed to find a proof for Theorem ' + theoremName + '.'
    );
}

export function showSearchFailureMessageHole(hole: vscode.Position) {
    vscode.window.showInformationMessage(
        `Coqpilot failed to find a proof for hole at line ${hole.line + 1}.`
    );
}

export function showClientNotRunningMessage() {
    vscode.window.showInformationMessage(
        'Coqpilot is not running. Use the button in the bottom left corner to start it.'
    );
}

export function showReloadDueToEditorChange() {
    vscode.window.showInformationMessage(
        'Active coq file changed. Please reload Coqpilot to continue.'
    );
}

export function showExceptionMessage(msg: string) {
    vscode.window.showInformationMessage(
        'Coqpilot: An exception occured: ' + msg + '.'
    );
}

export function fileSnapshotRequired() {
    vscode.window.showInformationMessage(
        'Coqpilot requires a snapshot of the current file to be aware of the present theorems.',
        'Initialize and continue',
        'Cancel'
    ).then((value) => {
        if (value === 'Initialize and continue') {
            vscode.commands.executeCommand('coqpilot.init_history');
        }
    });
}

export function showNoGoalMessage() {
    vscode.window.showInformationMessage(
        'No goal to prove under the cursor. Please place the cursor inside a goal.'
    );
}

export function showSearchSucessMessage(editor: vscode.TextEditor, proof: string, position: vscode.Position) {
    editor.edit((editBuilder) => {
        editBuilder.insert(position, proof);
    });
}

export function showHoleSubstitutionSummaryMessage(
    theoremName: string, 
    provenHolesNum: number,
) {
    vscode.window.showInformationMessage(
        'Coqpilot was able to substitute ' + provenHolesNum + ' holes in Theorem ' + theoremName + '.'
    );
}

export function cleanAuxFiles() {
    // Glob *_cp_aux.v files and delete them
    const workspaceFolders = vscode.workspace.workspaceFolders;
    if (!workspaceFolders) {
        return;
    }

    workspaceFolders.forEach((folder) => {
        glob('**/*_cp_aux.v', { sync: false, cwd: folder.uri.fsPath }, (err, files) => {
            if (err) {
                return;
            }

            files.forEach((file) => {
                const filePath = path.resolve(folder.uri.fsPath, file);
                logger.info(`Deleting aux file ${filePath}`);
                vscode.workspace.fs.delete(vscode.Uri.file(filePath));
            });
        });
    });
}

export async function addAuxFilesToGitIgnore() {
    const workspaceFolders = vscode.workspace.workspaceFolders;

    if (!workspaceFolders) {
        return;
    }

    for (const folder of workspaceFolders) {
        const gitIgnorePath = path.join(folder.uri.fsPath, '.gitignore');
        if (!fs.existsSync(gitIgnorePath)) {
            logger.info(`.gitignore not found in ${folder.uri.fsPath}, skipping aux file addition`);
            // .gitignore not found. Exit.
            return;
        }

        logger.info(`.gitignore found in ${folder.uri.fsPath}`);

        const data = fs.readFileSync(gitIgnorePath, 'utf8');
        const auxExt = '*_cp_aux.v';
        if (data.indexOf(auxExt) === -1) {
            // Not found. Ask user if we should add it.
            logger.info("Aux file extension not found in .gitignore, asking user");
            await vscode.window.showInformationMessage(
                'Do you want to add "*_cp_aux.v" to .gitignore?', 
                'Yes', 
                'No'
            ).then((choice) => {
                if(choice === 'Yes') {
                    const rule = `\n# Coqpilot auxiliary files\n${auxExt}`;
                    fs.appendFile(gitIgnorePath, rule, (err) => {
                        if (err) {
                            vscode.window.showErrorMessage(`Unexpected error writing to .gitignore: ${err.message}`);
                        } else {
                            vscode.window.showInformationMessage('Successfully added "*_cp_aux.v" to .gitignore');
                        }
                    });
                }
            });
        } else {
            logger.info(`Aux file extension ${auxExt} already in .gitignore, skipping`);
        }
    }
}