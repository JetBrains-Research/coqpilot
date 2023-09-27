import * as assert from 'assert';
import { mockConfigRealGpt } from "../mock/mockConfig";
import * as path from 'path';

suite('Performance on IMM tests', () => {
	test('Run completions', async () => {
        const apiKey: string | undefined = process.env['TEST_ARG-key'];
        const immRoot: string | undefined = process.env['TEST_ARG-imm_root'];
        if (!immRoot) {
            assert.fail("imm_root is not defined");
        } else if (!apiKey) {
            assert.fail("key is not defined");
        }

        const coqFilePath = path.join(immRoot, 'src', 'basic', 'Execution.v');
        const config = mockConfigRealGpt(coqFilePath, immRoot, apiKey);

        console.log("config", config);

	}).timeout(5000);
});