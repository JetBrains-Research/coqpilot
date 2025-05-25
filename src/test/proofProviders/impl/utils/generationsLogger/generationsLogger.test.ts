import { expect } from "earl";

import {
    AnalyzedChatHistory,
    ChatHistory,
    EstimatedTokens,
} from "../../../../../proofProviders/impl/commonStructures/chat";
import { GeneratedRawContentItem } from "../../../../../proofProviders/impl/commonStructures/generatedRawContent";
import {
    GenerationTokens,
    constructGenerationTokens,
} from "../../../../../proofProviders/impl/commonStructures/generationTokens";
import { ProofGenerationType } from "../../../../../proofProviders/impl/commonStructures/proofGenerationType";
import {
    ProofProviderRequest,
    ProofProviderRequestFailed,
    ProofProviderRequestSucceeded,
} from "../../../../../proofProviders/impl/commonStructures/proofProviderRequest";
import {
    ModelParams,
    OpenAiModelParams,
    PredefinedProofsModelParams,
} from "../../../../../proofProviders/impl/modelParams";
import {
    GenerationsLogger,
    GenerationsLoggerSettings,
} from "../../../../../proofProviders/impl/utils/generationsLogger/generationsLogger";
import {
    DebugLoggerRecord,
    LoggerRecord,
} from "../../../../../proofProviders/impl/utils/generationsLogger/loggerRecord";
import { SyncFile } from "../../../../../proofProviders/impl/utils/generationsLogger/syncFile";
import {
    ConfigurationError,
    GenerationFailedError,
    ProofProviderError,
} from "../../../../../proofProviders/proofProviderErrors";

import { createTmpFile } from "../../../../../utils/fs/tmpFs";
import { nowTimestampMillis } from "../../../../../utils/time";
import {
    gptModelName,
    testModelId,
} from "../../../proofProvidersSpecificTestUtils/constants";
import { DummyProofProvider } from "../../../proofProvidersSpecificTestUtils/dummyProofProvider";

suite("[ProofProvider-s utils] GenerationsLogger test", () => {
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
        maxContextTheoremsNumber: Number.MAX_SAFE_INTEGER,
        multiroundProfile: {
            maxRoundsNumber: 1,
            defaultProofFixChoices: 1,
            proofFixPrompt: "fix it",
            maxPreviousProofVersionsNumber: Number.MAX_SAFE_INTEGER,
        },
        defaultChoices: 1,
    };
    const mockParams: PredefinedProofsModelParams = {
        ...mockParamsBase,
        tactics: predefinedProofs,
    };
    const mockOpenAiParams: OpenAiModelParams = {
        ...mockParamsBase,
        modelName: gptModelName,
        apiKey: "very sensitive api key",
        temperature: 1,
    };
    // different from `defaultChoices`, it's a real-life case
    const mockChoices = 2;
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
    const mockContextTheorems = ["test_theorm", "another_theorem"];
    const mockEstimatedTokens: EstimatedTokens = {
        messagesTokens: 100,
        maxTokensToGenerate: 80,
        maxTokensInTotal: 180,
    };
    const analyzedMockChat: AnalyzedChatHistory = {
        chat: mockChat,
        contextTheorems: mockContextTheorems,
        estimatedTokens: mockEstimatedTokens,
    };

    const mockProofs = ["auto.\nintro.", "auto."];
    const mockGenerationTokensSpent: GenerationTokens =
        constructGenerationTokens(
            mockEstimatedTokens.messagesTokens,
            mockEstimatedTokens.maxTokensToGenerate
        );
    const mockGeneratedRawProofs: GeneratedRawContentItem[] = mockProofs.map(
        (proofContent) => {
            return {
                content: proofContent,
                tokensSpent: constructGenerationTokens(
                    mockEstimatedTokens.messagesTokens,
                    5
                ),
            };
        }
    );

    async function withGenerationsLogger(
        settings: GenerationsLoggerSettings,
        block: (generationsLogger: GenerationsLogger) => Promise<void>
    ): Promise<void> {
        const generationsLogger = new GenerationsLogger(
            createTmpFile(),
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
        const proofProvider = new DummyProofProvider(generationsLogger);
        const mockRequest: ProofProviderRequest = {
            proofProvider: proofProvider,
            proofGenerationType: ProofGenerationType.CHAT_BASED,
            params: params,
            choices: mockChoices,
            analyzedChat: analyzedMockChat,
        };
        return mockRequest;
    }

    function succeeded(
        mockRequest: ProofProviderRequest
    ): ProofProviderRequestSucceeded {
        return {
            ...mockRequest,
            generatedRawProofs: mockGeneratedRawProofs,
            tokensSpentInTotal: mockGenerationTokensSpent,
        };
    }

    function failed(
        mockRequest: ProofProviderRequest,
        error: Error
    ): ProofProviderRequestFailed {
        return {
            ...mockRequest,
            proofProviderError: new GenerationFailedError(error),
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
        });

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

            class DummyProofProviderError extends ProofProviderError {
                constructor() {
                    super("dummy");
                    Object.setPrototypeOf(this, new.target.prototype);
                    this.name = "DummyProofProviderError";
                }
            }
            expect(() =>
                generationsLogger.logGenerationFailed(
                    failed(mockRequest, new DummyProofProviderError())
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
            mockEstimatedTokens,
            mockGenerationTokensSpent
        );
        expect(
            LoggerRecord.deserealizeFromString(loggerRecord.serializeToString())
        ).toEqual([loggerRecord, ""]);

        const debugLoggerRecord = new DebugLoggerRecord(
            loggerRecord,
            mockContextTheorems,
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
            undefined,
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
            mockContextTheorems,
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
            undefined,
            undefined
        );
        expect(
            LoggerRecord.deserealizeFromString(loggerRecord.serializeToString())
        ).toEqual([loggerRecord, ""]);

        const debugLoggerRecord = new DebugLoggerRecord(
            loggerRecord,
            undefined,
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
                undefined,
                undefined
            ),
            [], // empty context theorems list
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
