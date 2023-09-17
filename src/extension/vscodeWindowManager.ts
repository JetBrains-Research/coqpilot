import * as vscode from 'vscode';
import * as path from 'path';
import { CoqEditorUtils } from './coqEditorUtils';
import { Interactor } from '../coqLlmInteraction/interactor';
import { CoqPromptKShot } from '../coqLlmInteraction/coqLlmPrompt';
import { GPT35 } from '../coqLlmInteraction/gpt35';
import * as assert from 'assert';
import { VsCodeProgressBar, VsCodeSpinningWheelProgressBar } from './vscodeProgressBar';

export class VsCodeWindowManager {
    private coqEditorUtils: CoqEditorUtils;
    private coqLlmInteractor: Interactor | undefined;
    private readonly observedFilePath: string; 
    private admittedTheorems: string[] = [];

    private constructor() {
        this.coqEditorUtils = new CoqEditorUtils(vscode.window.activeTextEditor);  
        let editor = vscode.window.activeTextEditor;
        if (!editor) {
            return;
        }
        this.observedFilePath = editor.document.uri.path;
    }

    static async init(startProvingOnInit: boolean = false): Promise<VsCodeWindowManager | null> {
        const manager = new VsCodeWindowManager();

        const editor = vscode.window.activeTextEditor; 
        if (!editor) { 
            manager.showIncorrectFileFormatMessage(); return null;
        } else if (manager.observedFilePath !== editor.document.uri.path) { 
            manager.showReloadDueToEditorChange(); return null;
        } else if (!manager.checkRequirements()) {
            manager.showApiKeyNotProvidedMessage(); return null;
        }
        
        const openaiApiKey: string = vscode.workspace.getConfiguration('coqpilot')
                                                     .get('openaiApiKey') ?? "None";
		const numberOfShots: string = vscode.workspace.getConfiguration('coqpilot')
                                                     .get('proofAttemsPerOneTheorem') ?? "15";
        const numberOfTokens: number = 40000;
        const logAttempts: boolean = true;

        const coqFilePath = editor.document.uri.path;
        let coqFileRootDir = path.dirname(coqFilePath);
        
        let wsFolders = vscode.workspace.workspaceFolders;
        if (wsFolders && wsFolders.length > 0) {
            coqFileRootDir = wsFolders[0].uri.path;
        }
        
        const progressIndicatorPercentage = new VsCodeProgressBar();
        const progressIndicatorSpinningWheel = new VsCodeSpinningWheelProgressBar();
        const llmPrompt = await CoqPromptKShot.init(
            coqFilePath, coqFileRootDir, numberOfTokens,
            undefined, progressIndicatorPercentage
        );
        const llmInterface = new GPT35(openaiApiKey);
        manager.coqLlmInteractor = new Interactor(
            llmPrompt, 
            llmInterface, 
            progressIndicatorSpinningWheel,
            logAttempts, 
            parseInt(numberOfShots)
        ); 
        manager.admittedTheorems = llmPrompt.getAdmittedTheorems();

        manager.showParsingFinishedMessage();

        if (startProvingOnInit) {
            for (let i = 0; i < manager.admittedTheorems.length; i++) {
                await manager.tryProveTheorem(manager.admittedTheorems[i]);
            }
        }

        return manager;
    }

    async tryProveAll() {
        for (let i = 0; i < this.admittedTheorems.length; i++) {
            await this.tryProveTheorem(this.admittedTheorems[i]);
        }
    }

    async tryProveTheorem(thrName: string) {
        console.log("tryProveTheorem " + thrName);
        const editor = vscode.window.activeTextEditor;
        if (editor.document.uri.path !== this.observedFilePath) {
            this.showReloadDueToEditorChange(); return; 
        }
        assert(this.coqLlmInteractor);

        const [thrStatement, proof] = await this.coqLlmInteractor.runCompleteProofGerenation(thrName);
        const proofText = `${thrStatement}\n${proof}`;
        if (proof) {
            this.showSearchSucessMessage(thrName, proofText);
        } else {
            this.showSearchFailureMessage(thrName);
        }
    }

    async tryProveBySelection() {
        let theoremName = this.coqEditorUtils.findTheoremInSelection();
        if (!theoremName) {
            this.noTheoremInSelectionMessage(); return;
        } 
        if (!this.coqLlmInteractor) {
            this.fileSnapshotRequired(); return;
        }

        this.tryProveTheorem(theoremName);
    }

    async holeSubstitutionInSelection() {
        let theoremName = this.coqEditorUtils.findTheoremInSelection();
        if (!theoremName) {
            this.noTheoremInSelectionMessage(); return;
        } 
        if (!this.coqLlmInteractor) {
            this.fileSnapshotRequired(); return;
        }

        const holesNum = this.coqLlmInteractor.getHolesNum(theoremName);
        for (let i = 0; i < holesNum; i++) {
            const [thrStatement, proof] = await this.coqLlmInteractor.runHoleSubstitution(theoremName, i);
            const proofText = `${thrStatement}\n${proof}`;

            if (proof) {
                const [tactic, holeRange] = this.coqLlmInteractor.getAuxTheoremApplyTactic(theoremName, i);
                const vscodeHoleRange = new vscode.Range(
                    holeRange.start.line, holeRange.start.character,
                    holeRange.end.line, holeRange.end.character
                );
                await this.coqEditorUtils.insertAboveTheorem(theoremName, proofText);
                this.coqEditorUtils.insertIntoHole(theoremName, vscodeHoleRange, tactic);
            } else {
                // TODO: show error message   
            }
        }
    }

    async showApiKeyNotProvidedMessage() {
        await vscode.window.showInformationMessage(
            'Please set your OpenAI API key in the settings.', 
            'Open settings'
        ).then((value) => {
            if (value === 'Open settings') {
                vscode.commands.executeCommand('workbench.action.openSettings', 'coqpilot.openaiApiKey');
            }
        });
    }

    async showParsingFinishedMessage() {
        await vscode.window.showInformationMessage(
            'File analysis finished successfully.'
        );
    }

    async showIncorrectFileFormatMessage() {
        await vscode.window.showInformationMessage(
            'Please open a Coq file first.'
        );
    }

    async noTheoremInSelectionMessage() {
        await vscode.window.showInformationMessage(
            'Please select a theorem to prove. Select it by highlighting the whole theorem, including the Admitted.'
        );
    }

    async showSearchFailureMessage(theoremName: string) {
        await vscode.window.showInformationMessage(
            'Coqpilot failed to find a proof for Theorem ' + theoremName + '.'
        );
    }

    async showReloadDueToEditorChange() {
        await vscode.window.showInformationMessage(
            'Active coq file changed. Please reload Coqpilot to continue.'
        );
    }

    async fileSnapshotRequired() {
        await vscode.window.showInformationMessage(
            'Coqpilot requires a snapshot of the current file to be aware of the present theorems. ' +
            'Coqpilot will firsly analyze the file. Please wait.'
        );
    }

    async showSearchSucessMessage(theoremName: string, proof: string) {
        let editor = vscode.window.activeTextEditor;

        await vscode.window.showInformationMessage(
			'Coqpilot found a proof for Theorem ' + theoremName + '.',
			'Accept',
			'Reject'
		).then((value) => {
			if (value === 'Accept' && editor) {
				let theoremRange = this.coqEditorUtils.getTheoremRange(theoremName);
                if (theoremRange) {
                    this.coqEditorUtils.insertIntoRange(theoremRange, proof);
                }
			}
		});
    }

    checkRequirements(): boolean {
        let editor = vscode.window.activeTextEditor;

		if (!editor || editor.document.languageId !== 'coq') {
            this.showIncorrectFileFormatMessage();
            return false;
		} 

        const openaiApiKey: string | undefined = vscode.workspace.getConfiguration('coqpilot')
                                                                 .get('openaiApiKey');
        if (openaiApiKey === undefined) {
            this.showApiKeyNotProvidedMessage();
            return false;
        }

        return true;
    }

    finish() {
        this.coqLlmInteractor?.stop();
    }
}