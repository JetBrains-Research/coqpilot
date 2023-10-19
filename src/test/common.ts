import * as vscode from 'vscode';

export async function openTextFile(docUri : vscode.Uri) : Promise<vscode.Uri> {
    const doc = await vscode.workspace.openTextDocument(docUri);
    await vscode.window.showTextDocument(doc, { preview : false });
    return docUri;
}

export async function sleep(ms: number) {
	return new Promise(resolve => setTimeout(resolve, ms));
}