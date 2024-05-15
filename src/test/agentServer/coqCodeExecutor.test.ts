import { expect } from "earl";
import * as fs from "fs";
import * as path from "path";
import { Position } from "vscode-languageclient";

import { CoqCodeExecutor } from "../../agentServer/services/coqCommandExecutor";
import { createCoqLspClient } from "../commonTestFunctions";

import { serverRunRoot } from "./commonServerTestFunctions";

suite("AgentServer: CoqCodeExecutor test that no aux files are left", () => {
    async function countFiles(rootDir: string): Promise<number> {
        let count = 0;
        const entries = await fs.promises.readdir(rootDir, {
            withFileTypes: true,
        });

        for (const entry of entries) {
            if (entry.isDirectory()) {
                count += await countFiles(path.join(rootDir, entry.name)); // Recurse into subdirectories
            } else if (entry.isFile()) {
                count += 1;
            }
        }

        return count;
    }

    test("Check that no aux files are spawned after correct run", async () => {
        const coqLspClient = createCoqLspClient();
        const executor = new CoqCodeExecutor(coqLspClient);
        const position: Position = {
            line: 0,
            character: 0,
        };

        const filesBefore = await countFiles(serverRunRoot);
        const result = await executor.executeCoqCommand(
            serverRunRoot,
            [""],
            position,
            "Check nat."
        );
        const filesAfter = await countFiles(serverRunRoot);

        expect(filesAfter).toEqual(filesBefore);
        expect(result.ok).toEqual(true);
        expect(result.val).toEqual(["nat\n     : Set"]);
    });

    test("Check that no aux files are spawned after run, that throws", async () => {
        const coqLspClient = createCoqLspClient();
        const executor = new CoqCodeExecutor(coqLspClient);
        const position: Position = {
            line: 0,
            character: 0,
        };

        const filesBefore = await countFiles(serverRunRoot);
        const result = await executor.executeCoqCommand(
            serverRunRoot,
            [""],
            position,
            "Check not_existant."
        );
        const filesAfter = await countFiles(serverRunRoot);

        expect(filesAfter).toEqual(filesBefore);
        expect(result.err).toEqual(true);
        expect(result.val).toEqual(
            "The reference not_existant was not found in the current\nenvironment."
        );
    });
});
