import { expect } from "earl";
import * as path from "path";
import * as tmp from "tmp";

import { PredefinedProofsModelParams } from "../../llm/llmServices/modelParams";
import {
    FromChatGenerationRequest,
    RequestsLogger,
} from "../../llm/llmServices/utils/requestsLogger/requestsLogger";

suite("RequestsLogger test", () => {
    const logsTestDir = tmp.dirSync().name;
    const filePath = path.join(logsTestDir, "predefinedLogs.txt");
    const printParsedLogsToConsole = false;

    const predefinedProofs = [
        "intros.",
        "reflexivity.",
        "auto.",
        "assumption. intros.",
        "left. reflexivity.",
    ];
    const params: PredefinedProofsModelParams = {
        tactics: predefinedProofs,
        modelName: "test model",
        systemPrompt: "hi system",
        newMessageMaxTokens: 10000,
        tokensLimit: 1000000,
        multiroundProfile: {
            maxRoundsNumber: 1,
            proofFixChoices: 1,
            proofFixPrompt: "fix it",
        },
    };
    const request: FromChatGenerationRequest = {
        chat: [
            {
                role: "system",
                content: "hello from system!",
            },
            {
                role: "user",
                content: "hello from user!\nI love multiline!",
            },
            {
                role: "assistant",
                content: "hello from assistant!",
            },
        ],
        estimatedTokens: 100,
        params: params,
        choices: 2,
    };
    const generatedProofs = ["auto.\nintro.", "auto."];

    const debug = true;
    const requestLogger = new RequestsLogger(filePath, debug);

    async function writeLogs(): Promise<void> {
        requestLogger.logRequestSucceeded(request, generatedProofs);
        requestLogger.logRequestSucceeded(request, generatedProofs);
        requestLogger.logRequestFailed(request, Error("network failed"));
        requestLogger.logRequestFailed(
            request,
            Error("tokens limit exceeded\nunfortunately, many times")
        );
    }

    function readAndCheckLogs(expectedRecordsLength: number) {
        const records = requestLogger.readLogs();
        if (printParsedLogsToConsole) {
            console.log(`PARSED RECORDS:\n${records}\n`);
        }
        expect(records.length).toEqual(expectedRecordsLength);
    }

    test("Simple write-read", async () => {
        requestLogger.resetLogs();
        await writeLogs();
        readAndCheckLogs(debug ? 4 : 3);
    });

    test("Pseudo-concurrent write-read", async () => {
        requestLogger.resetLogs();
        const logsWriters = [];
        const logsWritersN = 50;
        for (let i = 0; i < logsWritersN; i++) {
            logsWriters.push(writeLogs());
        }
        Promise.all(logsWriters);
        readAndCheckLogs(debug ? 4 * logsWritersN : 3);
    });
});
