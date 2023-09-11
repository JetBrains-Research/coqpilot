import * as assert from 'assert';
import * as coqlsp from 'coqlsp-client';

import * as path from 'path';
import * as vscode from 'vscode';

suite('Integration tests', () => {
	vscode.window.showInformationMessage('Start all tests.');

	test('Coq-lsp dependency simple test', async () => {
        const dirname = path.dirname(path.dirname(path.dirname(__dirname)));
		const filePath = path.join(dirname, 'src', 'test', 'resources', 'integration_test.v');        
        const parentDir = path.join(dirname, 'src', 'test', 'resources');

        const proofView = await coqlsp.ProofView.init(
            filePath,
            parentDir
        );

        const thrs = proofView.allTheoremNames();
        assert.strictEqual(thrs.length, 2);
        const ans = ['test_thr', 'test_thr1'];
        assert.deepStrictEqual(thrs, ans);
	});
});
