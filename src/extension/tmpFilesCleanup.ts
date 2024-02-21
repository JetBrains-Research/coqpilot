import {
    workspace,
    Uri
} from 'vscode';

import * as glob from 'glob';
import * as path from 'path';

export function hideAuxFiles() {
    // Hide files generated to check proofs
    let activationConfig = workspace.getConfiguration();
    let fexc: any = activationConfig.get("files.exclude");
    activationConfig.update("files.exclude", {
        ...fexc,
        // eslint-disable-next-line @typescript-eslint/naming-convention
        '**/*_cp_aux.v': true,
    });
}

export function cleanAuxFiles() {
    // Glob *_cp_aux.v files and delete them
    const workspaceFolders = workspace.workspaceFolders;
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
                workspace.fs.delete(Uri.file(filePath));
            });
        });
    });
}