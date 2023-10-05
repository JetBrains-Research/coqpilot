import * as assert from 'assert';
import { mockConfigRealGpt } from "../mock/mockConfig";

suite('Performance on IMM tests', () => {
	test('Run completions', async () => {
        const apiKey: string | undefined = process.env['TEST_ARG-key'];
        const immRoot: string | undefined = process.env['TEST_ARG-imm_root'];
        if (!immRoot) {
            assert.fail("imm_root is not defined");
        } else if (!apiKey) {
            assert.fail("key is not defined");
        }

        const config = mockConfigRealGpt(apiKey);

        console.log("config", config);

	}).timeout(5000);
});