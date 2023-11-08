import { 
    workspace, 
    commands, 
    window, 
    languages,
    Range
} from 'vscode';

import * as path from 'path';
import * as assert from 'assert';
import * as common from '../common';

suite('Simple single-tactic solver tests', () => {
    const dirname = path.dirname(path.dirname(path.dirname(__dirname)));

	test('Check prove using simple single-tactic prover', async () => {
        const { filePath, tacticsToTry, solvedAmount } = {
            filePath: path.join(dirname, 'src', 'test', 'resources', 'with_admits_test.v'),
            tacticsToTry: ['auto'], 
            solvedAmount: 6, 
        };

        // change the setting of useGpt to false
        await workspace.getConfiguration("coqpilot").update('useGpt', false);
        await workspace.getConfiguration("coqpilot").update('extraCommandsList', tacticsToTry);
        
        // vscode open filePath
        const doc = await workspace.openTextDocument(filePath);
        await window.showTextDocument(doc);
        await languages.setTextDocumentLanguage(doc, "coq");

        const text = doc.getText();
        const admitsBeforeGeneration = text.match(/admit./g)?.length ?? 0;

        await commands.executeCommand('coqpilot.init_history');
        await common.sleep(2000);

        await commands.executeCommand('coqpilot.prove_all_holes');
        await common.sleep(5000);

        // get the difference between document versions
        const admitsAfterGeneration = window.activeTextEditor?.document.getText().match(/admit./g)?.length ?? 0;
        const admitsDifference = admitsBeforeGeneration - admitsAfterGeneration;

        // modify text back to original
        await window.activeTextEditor?.edit(editBuilder => {
            editBuilder.replace(new Range(0, 0, doc.lineCount, 0), text);
        });

        assert.strictEqual(admitsDifference, solvedAmount);
    }).timeout(15000);
});