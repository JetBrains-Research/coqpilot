import * as assert from 'assert';
import { mockConfig } from "../mock/mockConfig";
import * as path from 'path';
import { CoqpilotState } from '../../extension/coqpilotState';

const sleep = (ms: number) => {
    return new Promise(resolve => setTimeout(resolve, ms));
};

suite('Coqpilot state tests', () => {
	test('Run multiple tasks', async () => {
        const dirname = path.dirname(path.dirname(path.dirname(__dirname)));
        const filePath = path.join(dirname, 'src', 'test', 'resources', 'interaction_test_1.v');
        const config = mockConfig(filePath);
        const state = await CoqpilotState.init(config);
        const start = performance.now();
        let operationsCompleted = 0;
        const timeSinceStart: number[] = [];

        state.tryProveTheorem('test', "Theorem test: True.").then((proof) => {
            const end = performance.now();
            timeSinceStart.push(end - start);
            assert.strictEqual(proof, 'Theorem test: True.\nProof. trivial. Qed.');
            operationsCompleted++;
        });

        state.tryProveTheorem('test2', "Theorem test2: False.").then((proof) => {
            const end = performance.now();
            timeSinceStart.push(end - start);
            assert.strictEqual(proof, undefined);
            operationsCompleted++;
        });

        state.tryProveTheorem('test3', "Theorem test3: 1 = 1.").then((proof) => {
            const end = performance.now();
            timeSinceStart.push(end - start);
            assert.strictEqual(proof, "Theorem test3: 1 = 1.\nProof. reflexivity. Qed.");
            operationsCompleted++;
        });

        while(operationsCompleted < 3) {
            await sleep(100);
        }

        for(let i = 0; i < timeSinceStart.length - 1; i++) {
            assert(timeSinceStart[i] <= timeSinceStart[i + 1]);
        }
	}).timeout(5000);
});