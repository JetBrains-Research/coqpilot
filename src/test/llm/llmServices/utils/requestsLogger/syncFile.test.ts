import { expect } from "earl";
import * as tmp from "tmp";

import { SyncFile } from "../../../../../llm/llmServices/utils/requestsLogger/syncFile";

suite("[LLMService-s utils] SyncFile test", () => {
    const filePath = tmp.fileSync().name;
    const file = new SyncFile(filePath);

    test("Basic operations", () => {
        if (file.exists()) {
            file.delete();
        }
        expect(file.exists()).toBeFalsy();

        file.createReset();
        expect(file.exists()).toBeTruthy();

        file.append("- hello?\n");
        file.append("- coq!");
        expect(file.read()).toEqual("- hello?\n- coq!");

        file.write("only coq");
        expect(file.read()).toEqual("only coq");

        file.createReset();
        expect(file.read()).toEqual("");

        file.delete();
        expect(file.exists()).toBeFalsy();
    });

    async function appendManyLongLines(
        workerId: number,
        linesN: number
    ): Promise<string> {
        const lines = [];
        const longSuffix = "coq\t".repeat(100);
        for (let i = 0; i < linesN; i++) {
            lines.push(`${workerId}: ${longSuffix}\n`);
        }
        file.append(lines.join(""));
        return "done";
    }

    // Tests that `SyncFile` actually provides synchronization for async operations.
    test("Pseudo-concurrent operations", async () => {
        file.createReset();
        const workers = [];
        const workersN = 100;
        const linesN = 100;
        for (let i = 0; i < workersN; i++) {
            workers.push(appendManyLongLines(i, linesN));
        }
        const workersDone = await Promise.all(workers);
        expect(workersDone).toEqual(new Array(workersN).fill("done"));

        const lines = file.read().split("\n").slice(0, -1);
        expect(lines).toHaveLength(workersN * linesN);

        const workersLinesCnt: { [key: number]: number } = {};
        let lastLineWorkerId = -1;
        for (const line of lines) {
            const rawParts = line.split(":");
            expect(rawParts.length).toBeGreaterThan(1);
            const workerId = parseInt(rawParts[0]);

            if (workerId in workersLinesCnt) {
                expect(lastLineWorkerId).toEqual(workerId);
                workersLinesCnt[workerId] += 1;
            } else {
                if (lastLineWorkerId !== -1) {
                    expect(workersLinesCnt[lastLineWorkerId]).toEqual(linesN);
                }
                workersLinesCnt[workerId] = 1;
            }
            lastLineWorkerId = workerId;
        }

        for (let i = 0; i < workersN; i++) {
            expect(workersLinesCnt[i]).toEqual(linesN);
        }
    });
});
