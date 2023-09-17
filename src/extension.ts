import * as vscode from 'vscode';
import { VsCodeWindowManager } from './extension/vscodeWindowManager';

let windowManager: VsCodeWindowManager | null = null;

// When extension is activated the very first time the command is executed
export function activate(context: vscode.ExtensionContext) {
	console.log('Coqpilot is now active.');

	let startCommand = vscode.commands.registerCommand('coqpilot.start', async () => {
		try {
			windowManager = await VsCodeWindowManager.init();
		} catch (err) {
			console.log(err);
			return;
		}
	});

	let solveParticularCommand = vscode.commands.registerCommand('coqpilot.solve_by_selection', async () => {
		if (windowManager === null) {
			try {
				windowManager = await VsCodeWindowManager.init();
				await windowManager.tryProveBySelection();
				return;
			} catch (err) {
				console.log(err);
				vscode.window.showErrorMessage("Coqpilot failed to start. Please check the logs.");
				return;
			}
		} else {
			windowManager.tryProveBySelection();
		}
	});

	let solveHolesCommand = vscode.commands.registerCommand('coqpilot.substitute_holes', async () => {
		if (windowManager === null) {
			try {
				windowManager = await VsCodeWindowManager.init();
				await windowManager.holeSubstitutionInSelection();
				return;
			} catch (err) {
				console.log(err);
				vscode.window.showErrorMessage("Coqpilot failed to start. Please check the logs.");
				return;
			}
		} else {
			windowManager.holeSubstitutionInSelection();
		}
	});

	let tryProveAllCommand = vscode.commands.registerCommand('coqpilot.prove_all', async () => {
		if (windowManager === null) {
			try {
				windowManager = await VsCodeWindowManager.init();
				await windowManager.tryProveAll();
				return;
			} catch (err) {
				console.log(err);
				vscode.window.showErrorMessage("Coqpilot failed to start. Please check the logs.");
				return;
			}
		} else {
			windowManager.tryProveAll();
		}
	});

	let finishCommand = vscode.commands.registerCommand('coqpilot.finish', async () => {
		if (windowManager === null) {
			vscode.window.showErrorMessage("Coqpilot is not running.");
			return;
		} else {
			windowManager.finish();
		}
	});

	context.subscriptions.push(startCommand);
	context.subscriptions.push(solveParticularCommand);
	context.subscriptions.push(solveHolesCommand);
	context.subscriptions.push(tryProveAllCommand);
	context.subscriptions.push(finishCommand);
}

// This method is called when your extension is deactivated
export function deactivate() {
	if (windowManager !== null) {
		windowManager.finish();
	}
}