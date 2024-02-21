import {
    window,
    commands,
    workspace
} from "vscode";
import * as path from 'path';
import {
    existsSync, 
    readFileSync, 
    appendFile
} from 'fs';

export namespace EditorMessages {
    export const timeoutError = 'Coqpilot: The proof checking process timed out. Please try again.';
    export const noProofsForAdmit = (admitIdentifier: any) => `Coqpilot failed to find a proof for the admit at line ${admitIdentifier}.`;
    export const exceptionError = (errorMsg: string) => 'Coqpilot: An exception occured: ' + errorMsg;
}

export function showMessageToUser(
    message: string, 
    severity: 'error' | 'info' | 'warning' = 'info'
) {
    switch (severity) {
        case 'error':
            window.showErrorMessage(message);
            break;
        case 'info':
            window.showInformationMessage(message);
            break;
        case 'warning':
            window.showWarningMessage(message);
            break;
    }
}

export function showApiKeyNotProvidedMessage(
    service: 'openai' | 'grazie', 
    pluginId: string
) {
    const serviceParamSettingName = service === 'openai' ? 'openAiModelsParameters' : 'grazieModelsParameters'; 
    const serviceName = service === 'openai' ? 'Open Ai' : 'Grazie'; 

    window.showInformationMessage(
        `Please set your ${serviceName} API key in the settings.`, 
        'Open settings'
    ).then((value) => {
        if (value === 'Open settings') {
            commands.executeCommand('workbench.action.openSettings', `${pluginId}.${serviceParamSettingName}`);
        }
    });
}

export async function suggestAddingAuxFilesToGitignore() {
    const workspaceFolders = workspace.workspaceFolders;
    if (!workspaceFolders) {
        return;
    }

    for (const folder of workspaceFolders) {
        const gitIgnorePath = path.join(folder.uri.fsPath, '.gitignore');
        if (!existsSync(gitIgnorePath)) {
            // .gitignore not found. Exit.
            return;
        }

        const data = readFileSync(gitIgnorePath, 'utf8');
        const auxExt = '*_cp_aux.v';
        if (data.indexOf(auxExt) === -1) {
            // Not found. Ask user if we should add it.
            await window.showInformationMessage(
                'Do you want to add "*_cp_aux.v" to .gitignore?', 
                'Yes', 
                'No'
            ).then((choice) => {
                if(choice === 'Yes') {
                    const rule = `\n# Coqpilot auxiliary files\n${auxExt}`;
                    appendFile(gitIgnorePath, rule, (err) => {
                        if (err) {
                            showMessageToUser(`Unexpected error writing to .gitignore: ${err.message}`, 'error');
                        } else {
                            showMessageToUser('Successfully added "*_cp_aux.v" to .gitignore');
                        }
                    });
                }
            });
        } else {
            return;
        }
    }
}