import { SingleTacticSolver } from '../../coqLlmInteraction/singleTacticSolver';
import { VsCodeSpinningWheelProgressBar } from '../../extension/vscodeProgressBar';
import { MockLlmPrompt } from '../mock/mockllm';
import { CoqpilotConfig, CoqpilotConfigWrapper } from '../../extension/config';
import { workspace } from 'vscode';
import { LLMIterator } from '../../coqLlmInteraction/llmIterator';
import * as assert from 'assert';

suite('LLM Iterator tests', () => {
    const wsConfig = workspace.getConfiguration("coqpilot");

	test('Check iterator fetches all the values', async () => {
        const baseConf = CoqpilotConfig.create(wsConfig);
        const config: CoqpilotConfig = {
            ...baseConf,
            extraCommandsList: ['constructor.', 'kek.'],
        };

        const extensionConfig = new CoqpilotConfigWrapper(config, false);

        const mockLlm = new MockLlmPrompt();
        const solver = new SingleTacticSolver(extensionConfig);
        const progressBar = new VsCodeSpinningWheelProgressBar();

        const iterator = new LLMIterator([solver, mockLlm], 2, progressBar);
        const thrStatement = "Theorem test: True.";
        const answers = [
            "Proof. constructor. Qed.",
            "Proof. kek. Qed.", 
            "Proof. Qed.", 
            "Proof. trivial. Qed."
        ];

        let index = 0;
        while (true) {
            const result = await iterator.next(thrStatement);
            if (result.done) {
                break;
            }
            assert.strictEqual(answers[index], result.value.toString().replace(/\n/g, " "));
            index += 1;
        }
    });

    test('Check llm starts fetch only after step into its block', async () => {
        const baseConf = CoqpilotConfig.create(wsConfig);
        const config: CoqpilotConfig = {
            ...baseConf,
            extraCommandsList: ['auto.', 'ins.', 'desf.', 'trivial.'],
        };

        const extensionConfig = new CoqpilotConfigWrapper(config, false);
        const delay = 3000;

        const mockLlm = new MockLlmPrompt(delay);
        const mockLlm1 = new MockLlmPrompt(delay);
        const solver = new SingleTacticSolver(extensionConfig);
        const progressBar = new VsCodeSpinningWheelProgressBar();

        const iterator = new LLMIterator([solver, mockLlm, mockLlm1], 2, progressBar);
        const thrStatement = "Theorem test3: 1 = 1.";
        const answers = [
            "Proof. auto. Qed.", "Proof. ins. Qed.", "Proof. desf. Qed.", 
            "Proof. trivial. Qed.", "Proof. reflexivity. Qed.", "Proof. trivial. Qed.",
            "Proof. reflexivity. Qed.", "Proof. trivial. Qed."
        ];
        const expectedDelays = [0, 0, 0, 0, delay, 0, delay, 0];

        let index = 0;
        while (true) {
            const startTime = performance.now();
            const result = await iterator.next(thrStatement);
            const endTime = performance.now();
            const fetchDelay = endTime - startTime;
            if (result.done) {
                break;
            }
            assert.strictEqual(answers[index], result.value.toString().replace(/\n/g, " "));
            assert(fetchDelay >= expectedDelays[index] && fetchDelay < expectedDelays[index] + 800);
            index += 1;
        }
    }).timeout(10000);
});