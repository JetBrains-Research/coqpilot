import { expect } from "earl";
import * as tmp from "tmp";

import {
    ConfigurationError,
    GenerationFailedError,
    LLMServiceError,
} from "../../../../../llm/llmServiceErrors";
import { ChatHistory } from "../../../../../llm/llmServices/chat";
import {
    LLMServiceRequest,
    LLMServiceRequestFailed,
    LLMServiceRequestSucceeded,
} from "../../../../../llm/llmServices/llmService";
import {
    ModelParams,
    OpenAiModelParams,
    PredefinedProofsModelParams,
} from "../../../../../llm/llmServices/modelParams";
import {
    GenerationsLogger,
    GenerationsLoggerSettings,
} from "../../../../../llm/llmServices/utils/generationsLogger/generationsLogger";
import {
    DebugLoggerRecord,
    LoggerRecord,
} from "../../../../../llm/llmServices/utils/generationsLogger/loggerRecord";
import { SyncFile } from "../../../../../llm/llmServices/utils/generationsLogger/syncFile";
import { nowTimestampMillis } from "../../../../../llm/llmServices/utils/time";

import {
    gptTurboModelName,
    testModelId,
} from "../../../llmSpecificTestUtils/constants";
import { DummyLLMService } from "../../../llmSpecificTestUtils/dummyLLMService";

suite("[LLMService-s utils] GenerationsLogger test", () => {
    const predefinedProofs = [
        "intros.",
        "reflexivity.",
        "auto.",
        "auto.\nintro.",
    ];
    const mockParamsBase: ModelParams = {
        modelId: testModelId,
        systemPrompt: "hi system",
        maxTokensToGenerate: 10000,
        tokensLimit: 1000000,
        multiroundProfile: {
            maxRoundsNumber: 1,
            defaultProofFixChoices: 1,
            proofFixPrompt: "fix it",
        },
        defaultChoices: 1,
    };
    const mockParams: PredefinedProofsModelParams = {
        ...mockParamsBase,
        tactics: predefinedProofs,
    };
    const mockOpenAiParams: OpenAiModelParams = {
        ...mockParamsBase,
        modelName: gptTurboModelName,
        apiKey: "very sensitive api key",
        temperature: 1,
    };
    // different from `defaultChoices`, it's a real-life case
    const mockChoices = 2;
    const mockEstimatedTokens = 100;
    const mockChat: ChatHistory = [
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
    ];
    const mockProofs = ["auto.\nintro.", "auto."];

    async function withGenerationsLogger(
        settings: GenerationsLoggerSettings,
        block: (generationsLogger: GenerationsLogger) => Promise<void>
    ): Promise<void> {
        const generationsLogger = new GenerationsLogger(
            tmp.fileSync().name,
            settings
        );
        try {
            await block(generationsLogger);
        } finally {
            generationsLogger.dispose();
        }
    }

    async function withTestGenerationsLogger(
        loggerDebugMode: boolean,
        block: (generationsLogger: GenerationsLogger) => Promise<void>
    ): Promise<void> {
        return withGenerationsLogger(
            {
                debug: loggerDebugMode,
                paramsPropertiesToCensor: {},
                cleanLogsOnStart: true,
            },
            block
        );
    }

    function buildMockRequest(
        generationsLogger: GenerationsLogger,
        params: ModelParams = mockParams
    ) {
        const llmService = new DummyLLMService(generationsLogger);
        const mockRequest: LLMServiceRequest = {
            llmService: llmService,
            params: params,
            choices: mockChoices,
            analyzedChat: {
                chat: mockChat,
                estimatedTokens: mockEstimatedTokens,
            },
        };
        return mockRequest;
    }

    function succeeded(
        mockRequest: LLMServiceRequest
    ): LLMServiceRequestSucceeded {
        return {
            ...mockRequest,
            generatedRawProofs: mockProofs,
        };
    }

    function failed(
        mockRequest: LLMServiceRequest,
        error: Error
    ): LLMServiceRequestFailed {
        return {
            ...mockRequest,
            llmServiceError: new GenerationFailedError(error),
        };
    }

    async function writeLogs(
        generationsLogger: GenerationsLogger
    ): Promise<void> {
        const mockRequest = buildMockRequest(generationsLogger);
        generationsLogger.logGenerationSucceeded(succeeded(mockRequest));
        generationsLogger.logGenerationFailed(
            failed(mockRequest, Error("dns error"))
        );
        generationsLogger.logGenerationSucceeded(succeeded(mockRequest));
        generationsLogger.logGenerationFailed(
            failed(mockRequest, Error("network failed"))
        );
        generationsLogger.logGenerationFailed(
            failed(
                mockRequest,
                Error("tokens limit exceeded\nunfortunately, many times")
            )
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
        const testNamePostfix = loggerDebugMode
            ? "[debug true]"
            : "[debug false]";
        test(`Simple write-read ${testNamePostfix}`, async () => {
            await withTestGenerationsLogger(
                loggerDebugMode,
                async (generationsLogger) => {
                    await writeLogs(generationsLogger);
                    readAndCheckLogs(
                        loggerDebugMode ? 5 : 3,
                        generationsLogger
                    );
                }
            );
        });

        test(`Test \`readLogsSinceLastSuccess\` ${testNamePostfix}`, async () => {
            await withTestGenerationsLogger(
                loggerDebugMode,
                async (generationsLogger) => {
                    const noRecords =
                        generationsLogger.readLogsSinceLastSuccess();
                    expect(noRecords).toHaveLength(0);

                    await writeLogs(generationsLogger);
                    const records =
                        generationsLogger.readLogsSinceLastSuccess();
                    expect(records).toHaveLength(
                        logsSinceLastSuccessInclusiveCnt - 1
                    );
                }
            );

            test(`Test read no records ${testNamePostfix}`, async () => {
                await withTestGenerationsLogger(
                    loggerDebugMode,
                    async (generationsLogger) => {
                        expect(generationsLogger.readLogs()).toHaveLength(0);
                        expect(
                            generationsLogger.readLogsSinceLastSuccess()
                        ).toHaveLength(0);
                        generationsLogger.logGenerationSucceeded(
                            succeeded(buildMockRequest(generationsLogger))
                        );
                        expect(
                            generationsLogger.readLogsSinceLastSuccess()
                        ).toHaveLength(0);
                    }
                );
            });
        });

        test(`Pseudo-concurrent write-read ${testNamePostfix}`, async () => {
            await withTestGenerationsLogger(
                loggerDebugMode,
                async (generationsLogger) => {
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
                }
            );
        });
    });

    test("Throws on wrong error types", async () => {
        await withTestGenerationsLogger(true, async (generationsLogger) => {
            const mockRequest = buildMockRequest(generationsLogger);

            expect(() =>
                generationsLogger.logGenerationFailed(
                    failed(
                        mockRequest,
                        new ConfigurationError("invalid params")
                    )
                )
            ).toThrow(Error);

            class DummyLLMServiceError extends LLMServiceError {}
            expect(() =>
                generationsLogger.logGenerationFailed(
                    failed(mockRequest, new DummyLLMServiceError())
                )
            ).toThrow(Error);

            expect(() =>
                generationsLogger.logGenerationFailed(
                    failed(
                        mockRequest,
                        new GenerationFailedError(Error("double-wrapped error"))
                    )
                )
            ).toThrow(Error);
        });
    });

    test("Test censor params properties", async () => {
        const censorInt = -1;
        await withGenerationsLogger(
            {
                debug: true,
                paramsPropertiesToCensor: {
                    apiKey: GenerationsLogger.censorString,
                    tokensLimit: censorInt,
                },
                cleanLogsOnStart: true,
            },
            async (generationsLogger) => {
                const mockRequest = buildMockRequest(
                    generationsLogger,
                    mockOpenAiParams
                );
                generationsLogger.logGenerationSucceeded(
                    succeeded(mockRequest)
                );

                // test censorship via direct file read
                const fileContent = new SyncFile(
                    generationsLogger.filePath
                ).read();
                expect(
                    fileContent.includes(mockOpenAiParams.apiKey)
                ).toBeFalsy();
                expect(
                    fileContent.includes(`${mockOpenAiParams.tokensLimit}`)
                ).toBeFalsy();

                // test censorship via readLogs
                const records = generationsLogger.readLogs();
                expect(records).toHaveLength(1);
                const record = records[0] as DebugLoggerRecord;
                expect(record).not.toBeNullish();

                expect(record.params.tokensLimit).toEqual(censorInt);
                expect((record.params as OpenAiModelParams)?.apiKey).toEqual(
                    GenerationsLogger.censorString
                );
            }
        );
    });

    test("Test record serialization-deserealization: `SUCCESS`", async () => {
        const loggerRecord = new LoggerRecord(
            nowTimestampMillis(),
            mockParams.modelId,
            "SUCCESS",
            mockChoices,
            mockEstimatedTokens
        );
        expect(
            LoggerRecord.deserealizeFromString(loggerRecord.serializeToString())
        ).toEqual([loggerRecord, ""]);

        const debugLoggerRecord = new DebugLoggerRecord(
            loggerRecord,
            mockChat,
            mockParams,
            mockProofs
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
            mockChoices,
            mockEstimatedTokens,
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
            mockChat,
            mockParams
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
            mockChoices,
            undefined,
            undefined
        );
        expect(
            LoggerRecord.deserealizeFromString(loggerRecord.serializeToString())
        ).toEqual([loggerRecord, ""]);

        const debugLoggerRecord = new DebugLoggerRecord(
            loggerRecord,
            undefined,
            mockParams,
            undefined
        );
        expect(
            DebugLoggerRecord.deserealizeFromString(
                debugLoggerRecord.serializeToString()
            )
        ).toEqual([debugLoggerRecord, ""]);
    });

    test("Test record serialization-deserealization: empty lists", async () => {
        const debugLoggerRecord = new DebugLoggerRecord(
            new LoggerRecord(
                nowTimestampMillis(),
                mockParams.modelId,
                "SUCCESS",
                mockChoices,
                undefined,
                undefined
            ),
            [], // empty chat list
            mockParams,
            [] // empty generated proofs list
        );
        expect(
            DebugLoggerRecord.deserealizeFromString(
                debugLoggerRecord.serializeToString()
            )
        ).toEqual([debugLoggerRecord, ""]);
    });
});
