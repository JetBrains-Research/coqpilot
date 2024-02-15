import * as vscode from 'vscode';
import { CoqpilotConfig } from "../legacy_extension/config";

export async function openTextFile(docUri : vscode.Uri) : Promise<vscode.Uri> {
    const doc = await vscode.workspace.openTextDocument(docUri);
    await vscode.window.showTextDocument(doc, { preview : false });
    return docUri;
}

export async function sleep(ms: number) {
	return new Promise(resolve => setTimeout(resolve, ms));
}

export function updateCoqpilotConfig(config: CoqpilotConfig): CoqpilotConfig { 
    return {
        ...config,
        coqLspPath: process.env.COQ_LSP_PATH || "coq-lsp",
    };
}