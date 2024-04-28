import { expect } from "earl";
import * as tmp from "tmp";

import {
    AnalyzedChatHistory,
    ChatHistory,
} from "../../../llm/llmServices/chat";
import { LLMService } from "../../../llm/llmServices/llmService";
import { ResponseStatus } from "../../../llm/llmServices/utils/requestsLogger/loggerRecord";
import { UserMultiroundProfile } from "../../../llm/userModelParams";

import { EventLogger } from "../../../logging/eventLogger";

import { MockLLMModelParams, MockLLMService } from "./mockLLMService";

export const proofsToGenerate = [
    "auto.",
    "left. reflexivity.",
    "right. auto.",
    "intros.",
    "assumption.",
];

export const mockChat: AnalyzedChatHistory = {
    chat: [{ role: "system", content: "Generate proofs." }],
    estimatedTokens: 10,
};

export interface EventsTracker {
    mockGenerationEventsN: number;
    successfulGenerationEventsN: number;
    failedGenerationEventsN: number;
}

export function subscribeToTrackEvents(
    testEventLogger: EventLogger,
    mockService: MockLLMService,
    mockChat: AnalyzedChatHistory
): EventsTracker {
    const eventsTracker: EventsTracker = {
        mockGenerationEventsN: 0,
        successfulGenerationEventsN: 0,
        failedGenerationEventsN: 0,
    };
    testEventLogger.subscribeToLogicEvent(
        mockService.generationFromChatEvent,
        (chatData) => {
            expect(chatData as ChatHistory).toEqual(mockChat.chat);
            eventsTracker.mockGenerationEventsN += 1;
        }
    );
    testEventLogger.subscribeToLogicEvent(
        LLMService.generationSucceededEvent,
        (service) => {
            expect(service as MockLLMService).toEqual(mockService);
            eventsTracker.successfulGenerationEventsN += 1;
        }
    );
    testEventLogger.subscribeToLogicEvent(
        LLMService.generationFailedEvent,
        (service) => {
            expect(service as MockLLMService).toEqual(mockService);
            eventsTracker.failedGenerationEventsN += 1;
        }
    );
    return eventsTracker;
}

export interface ExpectedRecord {
    status: ResponseStatus;
    error?: Error;
}

export function expectLogs(
    expectedRecords: ExpectedRecord[],
    mockService: MockLLMService
) {
    const actualRecordsUnwrapped = mockService
        .readRequestsLogs()
        .map((record) => {
            return {
                status: record.responseStatus,
                error: record.error,
            };
        });
    const expectedRecordsUnwrapped = expectedRecords.map((record) => {
        return {
            status: record.status,
            error: record.error
                ? {
                      typeName: record.error.name,
                      message: record.error.message,
                  }
                : undefined,
        };
    });
    expect(actualRecordsUnwrapped).toEqual(expectedRecordsUnwrapped);
}

export function enhanceMockParams(
    basicMockParams: MockLLMModelParams,
    multiroundProfile: UserMultiroundProfile = {},
    unlimitedTokens: boolean = true
): MockLLMModelParams {
    return {
        ...basicMockParams,
        tokensLimit: unlimitedTokens ? 100_000 : basicMockParams.tokensLimit,
        multiroundProfile: {
            ...basicMockParams.multiroundProfile,
            ...multiroundProfile,
        },
    };
}

export async function withMockLLMService(
    block: (
        mockService: MockLLMService,
        basicMockParams: MockLLMModelParams,
        testEventLogger: EventLogger
    ) => Promise<void>
) {
    const testEventLogger = new EventLogger();
    const mockService = new MockLLMService(
        tmp.fileSync().name,
        testEventLogger,
        true
    );
    try {
        const basicMockParams: MockLLMModelParams = {
            modelName: "mock model",
            systemPrompt: mockService.systemPromptToOverrideWith,
            newMessageMaxTokens: 100,
            tokensLimit: 1000,
            multiroundProfile: {
                maxRoundsNumber: 1,
                proofFixChoices: 0,
                proofFixPrompt: "Fix proof",
            },
            proofsToGenerate: proofsToGenerate,
            resolvedWithMockLLMService: true,
        };
        await block(mockService, basicMockParams, testEventLogger);
    } finally {
        mockService.dispose();
    }
}
