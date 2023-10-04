import * as vscode from 'vscode';

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

export function showReloadDueToEditorChange() {
    vscode.window.showInformationMessage(
        'Active coq file changed. Please reload Coqpilot to continue.'
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

export function showSearchSucessMessage(editor: vscode.TextEditor, proof: string) {
    editor.edit((editBuilder) => {
        editBuilder.insert(editor.selection.active, proof);
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