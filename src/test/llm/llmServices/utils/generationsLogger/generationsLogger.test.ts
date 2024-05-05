import { expect } from "earl";
import * as path from "path";
import * as tmp from "tmp";

import { PredefinedProofsModelParams } from "../../../../../llm/llmServices/modelParams";
import {
    FromChatGenerationRequest,
    GenerationsLogger,
} from "../../../../../llm/llmServices/utils/generationsLogger/generationsLogger";
import {
    DebugLoggerRecord,
    LoggerRecord,
} from "../../../../../llm/llmServices/utils/generationsLogger/loggerRecord";
import { nowTimestampMillis } from "../../../../../llm/llmServices/utils/time";

import { testModelId } from "../../../llmSpecificTestUtils/constants";

suite("[LLMService-s utils] GenerationsLogger test", () => {
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
        modelId: testModelId,
        systemPrompt: "hi system",
        maxTokensToGenerate: 10000,
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

    async function writeLogs(
        generationsLogger: GenerationsLogger
    ): Promise<void> {
        generationsLogger.logGenerationSucceeded(
            mockRequest,
            mockGeneratedProofs
        );
        generationsLogger.logGenerationFailed(mockRequest, Error("dns error"));
        generationsLogger.logGenerationSucceeded(
            mockRequest,
            mockGeneratedProofs
        );
        generationsLogger.logGenerationFailed(
            mockRequest,
            Error("network failed")
        );
        generationsLogger.logGenerationFailed(
            mockRequest,
            Error("tokens limit exceeded\nunfortunately, many times")
        );
    }
    const logsSinceLastSuccessInclusiveCnt = 3;
    const logsWrittenInTotalCnt = 5;

    function readAndCheckLogs(
        expectedRecordsLength: number,
        generationsLogger: GenerationsLogger
    ) {
        const records = generationsLogger.readLogs();
        expect(records).toHaveLength(expectedRecordsLength);
    }

    [false, true].forEach((loggerDebugMode) => {
        const generationsLogger = new GenerationsLogger(
            filePath,
            loggerDebugMode
        );
        const testNamePostfix = loggerDebugMode
            ? "[debug true]"
            : "[debug false]";
        test(`Simple write-read ${testNamePostfix}`, async () => {
            generationsLogger.resetLogs();
            await writeLogs(generationsLogger);
            readAndCheckLogs(loggerDebugMode ? 5 : 3, generationsLogger);
        });

        test(`Test \`readLogsSinceLastSuccess\` ${testNamePostfix}`, async () => {
            generationsLogger.resetLogs();
            const noRecords = generationsLogger.readLogsSinceLastSuccess();
            expect(noRecords).toHaveLength(0);

            await writeLogs(generationsLogger);
            const records = generationsLogger.readLogsSinceLastSuccess();
            expect(records).toHaveLength(logsSinceLastSuccessInclusiveCnt - 1);
        });

        test(`Pseudo-concurrent write-read ${testNamePostfix}`, async () => {
            generationsLogger.resetLogs();
            const logsWriters = [];
            const logsWritersN = 50;
            for (let i = 0; i < logsWritersN; i++) {
                logsWriters.push(writeLogs(generationsLogger));
            }
            Promise.all(logsWriters);
            readAndCheckLogs(
                loggerDebugMode
                    ? logsWrittenInTotalCnt * logsWritersN
                    : logsSinceLastSuccessInclusiveCnt,
                generationsLogger
            );
        });
    });

    test("Test record serialization-deserealization: `SUCCESS`", async () => {
        const loggerRecord = new LoggerRecord(
            nowTimestampMillis(),
            mockParams.modelId,
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
            mockParams.modelId,
            "FAILURE",
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
            mockParams.modelId,
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
