import { SingleTacticSolver } from '../../coqLlmInteraction/singleTacticSolver';
import { VsCodeSpinningWheelProgressBar } from '../../extension/vscodeProgressBar';
import { MockLlm } from '../mock/mockllm';
import { CoqpilotConfig, CoqpilotConfigWrapper } from '../../extension/config';
import { workspace } from 'vscode';
import { LLMIterator } from '../../coqLlmInteraction/llmIterator';
import * as assert from 'assert';
import { LlmPromptBase } from '../../coqLlmInteraction/llmPromptInterface';
import { MockConfigWrapper, mockConfig } from '../mock/mockConfig';

suite('LLM Iterator tests', () => {
    const wsConfig = workspace.getConfiguration("coqpilot");

	test('Check iterator fetches all the values', async () => {
        const baseConf = CoqpilotConfig.create(wsConfig)!;
        const config: CoqpilotConfig = {
            ...baseConf,
            extraCommandsList: ['constructor.', 'kek.'],
        };

        const extensionConfig = new CoqpilotConfigWrapper(config, false);

        const mockLlm = new MockLlm();
        const solver = new SingleTacticSolver(extensionConfig);
        const progressBar = new VsCodeSpinningWheelProgressBar();

        const mockConf = new MockConfigWrapper(mockConfig());
        const iterator = new LLMIterator([solver, mockLlm], mockConf, progressBar);
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
            const answer = LlmPromptBase.thrProofToBullet(LlmPromptBase.removeBackticks(answers[index]));
            assert.strictEqual(answer, result.value.toString().replace(/\n/g, " "));
            index += 1;
        }
    });

    test('Check llm starts fetch only after step into its block', async () => {
        const baseConf = CoqpilotConfig.create(wsConfig)!;
        const config: CoqpilotConfig = {
            ...baseConf,
            extraCommandsList: ['auto.', 'ins.', 'desf.', 'trivial.'],
        };

        const extensionConfig = new CoqpilotConfigWrapper(config, false);
        const delay = 3000;

        const mockLlm = new MockLlm(delay);
        const mockLlm1 = new MockLlm(delay);
        const solver = new SingleTacticSolver(extensionConfig);
        const progressBar = new VsCodeSpinningWheelProgressBar();

        const mockConf = new MockConfigWrapper(mockConfig());
        const iterator = new LLMIterator([solver, mockLlm, mockLlm1], mockConf, progressBar);
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
            const answer = LlmPromptBase.thrProofToBullet(LlmPromptBase.removeBackticks(answers[index]));
            assert.strictEqual(answer, result.value.toString().replace(/\n/g, " "));
            assert(fetchDelay >= expectedDelays[index] && fetchDelay < expectedDelays[index] + 800);
            index += 1;
        }
    }).timeout(10000);
});