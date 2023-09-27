import * as vscode from 'vscode';
import { CoqEditorUtils } from './coqEditorUtils';
import { CoqpilotState } from './coqpilotState';
import { CoqpilotConfig } from './config';

let coqPilotState: CoqpilotState | undefined;

export class VsCodeWindowManager {
    private coqEditorUtils: CoqEditorUtils;
    private readonly observedFilePath: string; 
    private readonly config: CoqpilotConfig;

    private constructor(config: CoqpilotConfig) {
        this.coqEditorUtils = new CoqEditorUtils(vscode.window.activeTextEditor);  
        let editor = vscode.window.activeTextEditor;
        if (!editor) {
            return;
        }
        this.observedFilePath = editor.document.uri.path;
        this.config = config;
    }

    static async init(proveOnStartup: boolean | undefined = undefined): Promise<VsCodeWindowManager | null> {
        const editor = vscode.window.activeTextEditor; 
        const config = CoqpilotConfig.create(
            vscode.workspace.getConfiguration('coqpilot'),
            editor,
            vscode.workspace.workspaceFolders
        );

        const manager = new VsCodeWindowManager(config);

        if (!editor || editor.document.languageId !== 'coq') { 
            manager.showIncorrectFileFormatMessage(); return null;
        } else if (manager.observedFilePath !== editor.document.uri.path) { 
            manager.showReloadDueToEditorChange(); return null;
        } else if (config.openaiApiKey === "None") {
            manager.showApiKeyNotProvidedMessage(); return null;
        }

        CoqpilotConfig.checkRequirements(config);
        
        coqPilotState = await CoqpilotState.init(config);
        manager.showParsingFinishedMessage();

        if(proveOnStartup ?? config.proveAllOnStartup) {
            manager.proveAll();
        }

        return manager;
    }

    async proveAll() {
        if (!this.meetsRequirements()) { return; }
        for (let i = 0; i < coqPilotState?.admitted.length; i++) {
            const thrName = coqPilotState?.admitted[i];
            const proof = await coqPilotState?.tryProveTheorem(thrName);
            if (proof) {
                this.showSearchSucessMessage(thrName, proof);
            } else {
                this.showSearchFailureMessage(thrName);
            }
        }
    }

    async proveTheorem(thrName: string) {
        if (!this.meetsRequirements()) { return; }
        const proof = await coqPilotState?.tryProveTheorem(thrName);
        if (proof) {
            this.showSearchSucessMessage(thrName, proof);
        } else {
            this.showSearchFailureMessage(thrName);
        }
    }

    async tryProveBySelection() {
        if (!this.meetsRequirements()) { return; }
        let theoremName = this.coqEditorUtils.findTheoremInSelection();
        if (!theoremName) {
            this.noTheoremInSelectionMessage(); return;
        } 

        this.proveTheorem(theoremName);
    }

    async holeSubstitutionInSelection() {
        if (!this.meetsRequirements()) { return; }
        let theoremName = this.coqEditorUtils.findTheoremInSelection();
        if (!theoremName) {
            this.noTheoremInSelectionMessage(); return;
        } 

        const holesNum = coqPilotState?.getHolesNum(theoremName);
        let provenHolesNum = 0;
        for (let i = 0; i < holesNum; i++) {
            const proofText = await coqPilotState?.tryProveHole(theoremName, i);

            if (proofText) {
                provenHolesNum++;
                const [tactic, holeRange] = coqPilotState?.getHoleApplyTactic(theoremName, i);
                const vscodeHoleRange = new vscode.Range(
                    holeRange.start.line, holeRange.start.character,
                    holeRange.end.line, holeRange.end.character
                );

                if (!this.meetsRequirements()) { return; }
                if (this.config.proofHolesCreateAux) {
                    await this.coqEditorUtils.insertAboveTheorem(theoremName, proofText);
                    await this.coqEditorUtils.insertIntoHole(theoremName, vscodeHoleRange, tactic);
                } else {
                    const proofCleaned = this.coqEditorUtils.extractProofString(proofText);
                    await this.coqEditorUtils.insertIntoHole(theoremName, vscodeHoleRange, proofCleaned);
                }
            }
        }

        this.showHoleSubstitutionSummaryMessage(theoremName, provenHolesNum);
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
            'Coqpilot requires a snapshot of the current file to be aware of the present theorems.'
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
                if (!this.meetsRequirements()) { return; }
				let theoremRange = this.coqEditorUtils.getTheoremRange(theoremName);
                if (theoremRange) {
                    this.coqEditorUtils.insertIntoRange(theoremRange, proof);
                }
			}
		});
    }

    async showHoleSubstitutionSummaryMessage(
        theoremName: string, 
        provenHolesNum: number,
    ) {
        await vscode.window.showInformationMessage(
            'Coqpilot was able to substitute ' + provenHolesNum + ' holes in Theorem ' + theoremName + '.'
        );
    }

    meetsRequirements(): boolean {
        const editor = vscode.window.activeTextEditor;
        if (editor.document.uri.path !== this.observedFilePath) {
            this.showReloadDueToEditorChange(); return false;
        }
        if (!coqPilotState) {
            this.fileSnapshotRequired(); return false;
        }

        return true;
    }

    finish() {
        coqPilotState?.dispose();
        coqPilotState = undefined;
    }
}