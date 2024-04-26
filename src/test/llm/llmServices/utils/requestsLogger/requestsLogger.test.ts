import { expect } from "earl";
import * as path from "path";
import * as tmp from "tmp";

import { PredefinedProofsModelParams } from "../../../../../llm/llmServices/modelParams";
import {
    DebugLoggerRecord,
    LoggerRecord,
} from "../../../../../llm/llmServices/utils/requestsLogger/loggerRecord";
import {
    FromChatGenerationRequest,
    RequestsLogger,
} from "../../../../../llm/llmServices/utils/requestsLogger/requestsLogger";
import { nowTimestampMillis } from "../../../../../llm/llmServices/utils/time";

suite("[LLMService] RequestsLogger test", () => {
    const logsTestDir = tmp.dirSync().name;
    const filePath = path.join(logsTestDir, "testLogs.txt");

    const predefinedProofs = [
        "intros.",
        "reflexivity.",
        "auto.",
        "auto.\nintro.",
    ];
    const mockParams: PredefinedProofsModelParams = {
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
    const mockRequest: FromChatGenerationRequest = {
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
        params: mockParams,
        choices: 2,
    };
    const mockGeneratedProofs = ["auto.\nintro.", "auto."];

    async function writeLogs(requestsLogger: RequestsLogger): Promise<void> {
        requestsLogger.logRequestSucceeded(mockRequest, mockGeneratedProofs);
        requestsLogger.logRequestFailed(mockRequest, Error("dns error"));
        requestsLogger.logRequestSucceeded(mockRequest, mockGeneratedProofs);
        requestsLogger.logRequestFailed(mockRequest, Error("network failed"));
        requestsLogger.logRequestFailed(
            mockRequest,
            Error("tokens limit exceeded\nunfortunately, many times")
        );
    }
    const logsSinceLastSuccessCnt = 3;
    const logsWrittenInTotalCnt = 5;

    function readAndCheckLogs(
        expectedRecordsLength: number,
        requestsLogger: RequestsLogger
    ) {
        const records = requestsLogger.readLogs();
        expect(records).toHaveLength(expectedRecordsLength);
    }

    [false, true].forEach((loggerDebugMode) => {
        const requestsLogger = new RequestsLogger(filePath, loggerDebugMode);
        const testNamePostfix = loggerDebugMode
            ? "[debug true]"
            : "[debug false]";
        test(`Simple write-read ${testNamePostfix}`, async () => {
            requestsLogger.resetLogs();
            await writeLogs(requestsLogger);
            readAndCheckLogs(loggerDebugMode ? 5 : 3, requestsLogger);
        });

        test(`Test \`readLogsSinceLastSuccess\` ${testNamePostfix}`, async () => {
            requestsLogger.resetLogs();
            await writeLogs(requestsLogger);
            const records = requestsLogger.readLogsSinceLastSuccess();
            expect(records).toHaveLength(logsSinceLastSuccessCnt);
        });

        test(`Pseudo-concurrent write-read ${testNamePostfix}`, async () => {
            requestsLogger.resetLogs();
            const logsWriters = [];
            const logsWritersN = 50;
            for (let i = 0; i < logsWritersN; i++) {
                logsWriters.push(writeLogs(requestsLogger));
            }
            Promise.all(logsWriters);
            readAndCheckLogs(
                loggerDebugMode
                    ? logsWrittenInTotalCnt * logsWritersN
                    : logsSinceLastSuccessCnt,
                requestsLogger
            );
        });
    });

    test("Test record serialization-deserealization: `SUCCESS`", async () => {
        const loggerRecord = new LoggerRecord(
            nowTimestampMillis(),
            mockParams.modelName,
            "SUCCESS",
            mockRequest.choices,
            mockRequest.estimatedTokens
        );
        expect(
            LoggerRecord.deserealizeFromString(loggerRecord.serializeToString())
        ).toEqual([loggerRecord, ""]);

        const debugLoggerRecord = new DebugLoggerRecord(
            loggerRecord,
            mockRequest.chat,
            mockRequest.params,
            mockGeneratedProofs
        );
        expect(
            DebugLoggerRecord.deserealizeFromString(
                debugLoggerRecord.serializeToString()
            )
        ).toEqual([debugLoggerRecord, ""]);
    });

    test("Test record serialization-deserealization: `FAILED`", async () => {
        const error = Error("bad things happen");
        const loggerRecord = new LoggerRecord(
            nowTimestampMillis(),
            mockParams.modelName,
            "FAILED",
            mockRequest.choices,
            mockRequest.estimatedTokens,
            {
                typeName: error.name,
                message: error.message,
            }
        );
        expect(
            LoggerRecord.deserealizeFromString(loggerRecord.serializeToString())
        ).toEqual([loggerRecord, ""]);

        const debugLoggerRecord = new DebugLoggerRecord(
            loggerRecord,
            mockRequest.chat,
            mockRequest.params
        );
        expect(
            DebugLoggerRecord.deserealizeFromString(
                debugLoggerRecord.serializeToString()
            )
        ).toEqual([debugLoggerRecord, ""]);
    });

    test("Test record serialization-deserealization: undefined-s", async () => {
        const loggerRecord = new LoggerRecord(
            nowTimestampMillis(),
            mockParams.modelName,
            "SUCCESS",
            mockRequest.choices,
            undefined,
            undefined
        );
        expect(
            LoggerRecord.deserealizeFromString(loggerRecord.serializeToString())
        ).toEqual([loggerRecord, ""]);

        const debugLoggerRecord = new DebugLoggerRecord(
            loggerRecord,
            undefined,
            mockRequest.params,
            undefined
        );
        expect(
            DebugLoggerRecord.deserealizeFromString(
                debugLoggerRecord.serializeToString()
            )
        ).toEqual([debugLoggerRecord, ""]);
    });
});
