import * as vscode from 'vscode';
import { VsCodeWindowManager } from './extension/vscodeWindowManager';

let windowManager: VsCodeWindowManager | undefined;

export function activate(context: vscode.ExtensionContext) {
	console.log('Coqpilot is now active.');

	let test = vscode.commands.registerCommand('coqpilot.test', async () => {
		
	});

	let startCommand = vscode.commands.registerCommand('coqpilot.start', async () => {
		try {
			windowManager = await VsCodeWindowManager.init();
		} catch (err) {
			console.log(err);
			return;
		}
	});

	let solveParticularCommand = vscode.commands.registerCommand('coqpilot.solve_by_selection', async () => {
		if (!windowManager) {
			try {
				windowManager = await VsCodeWindowManager.init(false);
				await windowManager.tryProveBySelection();
				return;
			} catch (err) {
				console.log(err);
				vscode.window.showErrorMessage("Coqpilot failed to start. Please check the logs.");
				return;
			}
		} else {
			await windowManager.tryProveBySelection();
		}
	});

	let solveHolesCommand = vscode.commands.registerCommand('coqpilot.substitute_holes', async () => {
		if (!windowManager) {
			try {
				windowManager = await VsCodeWindowManager.init(false);
				await windowManager.holeSubstitutionInSelection();
				return;
			} catch (err) {
				console.log(err);
				vscode.window.showErrorMessage("Coqpilot failed to start. Please check the logs.");
				return;
			}
		} else {
			await windowManager.holeSubstitutionInSelection();
		}
	});

	let tryProveAllCommand = vscode.commands.registerCommand('coqpilot.prove_all', async () => {
		if (!windowManager) {
			try {
				windowManager = await VsCodeWindowManager.init(false);
				await windowManager.proveAll();
				return;
			} catch (err) {
				console.log(err);
				vscode.window.showErrorMessage("Coqpilot failed to start. Please check the logs.");
				return;
			}
		} else {
			await windowManager.proveAll();
		}
	});

	let finishCommand = vscode.commands.registerCommand('coqpilot.finish', async () => {
		if (!windowManager) {
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
	context.subscriptions.push(test);
}

export function deactivate() {
	windowManager?.finish();
}