import * as assert from 'assert';
import { Interactor } from '../../coqLlmInteraction/interactor';
import { MockLlmPrompt } from './mockllm';
import { CoqPromptKShot } from '../../coqLlmInteraction/coqLlmPrompt';
import { EvaluationLogger } from '../../coqLlmInteraction/evaluationLogger';
import { readFileSync, unlinkSync } from 'fs';
import { VsCodeSpinningWheelProgressBar } from '../../extension/vscodeProgressBar';
import dedent from "dedent";

import * as path from 'path';

suite('Interactor tests', () => {
	test('Check retrieve successful proof', async () => {
        const dirname = path.dirname(path.dirname(path.dirname(__dirname)));
		const filePath = path.join(dirname, 'src', 'test', 'resources', 'interaction_test_1.v');        
        const parentDir = path.join(dirname, 'src', 'test', 'resources');

        const llmPrompt = await CoqPromptKShot.init(
            filePath,
            parentDir,
            40000
        );
        const llmInterface = new MockLlmPrompt();

        const interactor = new Interactor(llmPrompt, llmInterface, new VsCodeSpinningWheelProgressBar(), false, 2);

        const [_s, proof1] = await interactor.runCompleteProofGerenation('test');
        assert.strictEqual(proof1, 'Proof. trivial. Qed.');

        const [_s1, proof2] = await interactor.runCompleteProofGerenation('test2');
        assert.strictEqual(proof2, undefined);

        const [_s2, proof3] = await interactor.runCompleteProofGerenation('test3');
        assert.strictEqual(proof3, 'Proof. reflexivity. Qed.');

        interactor.stop();
	});

    test('Check log 1 theorem proof attempt', async () => {
        const dirname = path.dirname(path.dirname(path.dirname(__dirname)));
        const dateTimeNow = EvaluationLogger.formatDate(new Date());
        
        const resFolder = path.join(dirname, 'src', 'test', 'resources');

        const filePath = path.join(dirname, 'src', 'test', 'resources', 'interaction_test_1.v');        
        const parentDir = path.join(dirname, 'src', 'test', 'resources');

        const llmPrompt = await CoqPromptKShot.init(
            filePath,
            parentDir,
            40000
        );
        const llmInterface = new MockLlmPrompt();

        const logFilePath = path.join(resFolder, `log_${dateTimeNow}.v`);
        const interactor = new Interactor(llmPrompt, llmInterface, new VsCodeSpinningWheelProgressBar(),  true, 2, resFolder);
        
        await interactor.runCompleteProofGerenation('test');
        interactor.stop();
        
        const logContents = readFileSync(logFilePath, 'utf8');
        const expectedContents = 
        dedent`
        (*
         Date: ${dateTimeNow}
         Strat: CoqPromptKShot
        *)
        
        (* {THEOREM PROOF LOG START} *)
        (* Attempt 1 for theorem test *)
        (*
        Theorem test: True.
        Proof. Qed.
        *)
        (* Attempt 1 for theorem test unsuccessful *)
        (* ERROR message:  (in proof test): Attempt to save an incomplete proof *)
        
        (* Attempt 2 for theorem test *)
        Theorem test: True.
        Proof. trivial. Qed.
        (* Attempt 2 for theorem test successful *)
        
        (* {THEOREM PROOF LOG END} *) 
        
        Theorem test2: False.
        Admitted.
        
        Theorem test3: 1 = 1.
        Admitted.
        `;

        assert.strictEqual(logContents, expectedContents);
        unlinkSync(logFilePath);
	});

    test('Check log multiple theorem proof attempts', async () => {
        const dirname = path.dirname(path.dirname(path.dirname(__dirname)));
        const dateTimeNow = EvaluationLogger.formatDate(new Date());
        
        const resFolder = path.join(dirname, 'src', 'test', 'resources');

        const filePath = path.join(dirname, 'src', 'test', 'resources', 'interaction_test_1.v');        
        const parentDir = path.join(dirname, 'src', 'test', 'resources');

        const llmPrompt = await CoqPromptKShot.init(
            filePath,
            parentDir,
            40000
        );
        const llmInterface = new MockLlmPrompt();

        const logFilePath = path.join(resFolder, `log_${dateTimeNow}.v`);
        const interactor = new Interactor(llmPrompt, llmInterface, new VsCodeSpinningWheelProgressBar(), true, 2, resFolder);
        
        await interactor.runCompleteProofGerenation('test');
        await interactor.runCompleteProofGerenation('test2');
        await interactor.runCompleteProofGerenation('test3');
        
        interactor.stop();
        
        const logContents = readFileSync(logFilePath, 'utf8');
        const expectedContents = 
        dedent`
        (*
         Date: ${dateTimeNow}
         Strat: CoqPromptKShot
        *)
        
        (* {THEOREM PROOF LOG START} *)
        (* Attempt 1 for theorem test *)
        (*
        Theorem test: True.
        Proof. Qed.
        *)
        (* Attempt 1 for theorem test unsuccessful *)
        (* ERROR message:  (in proof test): Attempt to save an incomplete proof *)
        
        (* Attempt 2 for theorem test *)
        Theorem test: True.
        Proof. trivial. Qed.
        (* Attempt 2 for theorem test successful *)
        
        (* {THEOREM PROOF LOG END} *) 
        
        (* {THEOREM PROOF LOG START} *)
        (* Attempt 1 for theorem test2 *)
        (*
        Theorem test2: False.
        Proof. trivial. Qed.
        *)
        (* Attempt 1 for theorem test2 unsuccessful *)
        (* ERROR message:  (in proof test2): Attempt to save an incomplete proof *)
        
        (* Attempt 2 for theorem test2 *)
        (*
        Theorem test2: False.
        Proof. trivial. Qed.
        *)
        (* Attempt 2 for theorem test2 unsuccessful *)
        (* ERROR message:  (in proof test2): Attempt to save an incomplete proof *)
        
        (* Correct proof was not found. This theorem will remain Admitted. *)
        Theorem test2: False.
        Admitted.
        (* {THEOREM PROOF LOG END} *)
        
        (* {THEOREM PROOF LOG START} *)
        (* Attempt 1 for theorem test3 *)
        Theorem test3: 1 = 1.
        Proof. reflexivity. Qed.
        (* Attempt 1 for theorem test3 successful *)
        
        (* {THEOREM PROOF LOG END} *)
        `;

        assert.strictEqual(logContents, expectedContents);
        unlinkSync(logFilePath);
	});
});
