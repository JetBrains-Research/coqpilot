import * as assert from 'assert';
import { Interactor } from '../../coqLlmInteraction/interactor';
import { MockLlmPrompt } from './mockllm';
import { CoqPromptKShot } from '../../coqLlmInteraction/coqLlmPrompt';

import * as path from 'path';

suite('Interactor tests', () => {
	test('Check retrieve successful proof', async () => {
        console.log("sv", __dirname);
        const dirname = path.dirname(path.dirname(path.dirname(__dirname)));
        console.log("sv", dirname);
		const filePath = path.join(dirname, 'src', 'test', 'resources', 'interaction_test_1.v');        
        const parentDir = path.join(dirname, 'src', 'test', 'resources');

        const llmPrompt = await CoqPromptKShot.init(
            filePath,
            parentDir,
            40000
        );
        const llmInterface = new MockLlmPrompt();

        const interactor = new Interactor(llmPrompt, llmInterface, false, 2);

        const proof1 = await interactor.runProofGeneration('test');
        assert.strictEqual(proof1, 'Proof. trivial. Qed.');

        const proof2 = await interactor.runProofGeneration('test2');
        assert.strictEqual(proof2, undefined);

        const proof3 = await interactor.runProofGeneration('test3');
        assert.strictEqual(proof3, 'Proof. reflexivity. Qed.');

        interactor.stop();
	});

    test('Check log 1 theorem proof attempt', async () => {
	});
});
