import { expect } from "earl";
import * as tmp from "tmp";

import {
    AnalyzedChatHistory,
    ChatHistory,
} from "../../../llm/llmServices/chat";
import {
    GeneratedProof,
    LLMService,
    ProofVersion,
} from "../../../llm/llmServices/llmService";
import { ResponseStatus } from "../../../llm/llmServices/utils/requestsLogger/loggerRecord";
import { ProofGenerationContext } from "../../../llm/proofGenerationContext";
import { UserMultiroundProfile } from "../../../llm/userModelParams";

import { EventLogger } from "../../../logging/eventLogger";

import { EventsTracker } from "./commonTestFunctions";
import {
    MockLLMGeneratedProof,
    MockLLMModelParams,
    MockLLMService,
} from "./mockLLMService";

export const proofsToGenerate = [
    "auto.",
    "left. reflexivity.",
    "right. auto.",
    "intros.",
    "assumption.",
    "something.",
    "",
    "reflexivity.",
    "auto.",
    "auto.",
];

export const mockChat: AnalyzedChatHistory = {
    chat: [{ role: "system", content: "Generate proofs." }],
    estimatedTokens: 10,
};

export const mockProofGenerationContext: ProofGenerationContext = {
    completionTarget: "forall n : nat, 0 + n = n",
    contextTheorems: [],
};

export interface MockEventsTracker extends EventsTracker {
    mockGenerationEventsN: number;
}

export function subscribeToTrackMockEvents(
    testEventLogger: EventLogger,
    mockService: MockLLMService,
    mockChat?: AnalyzedChatHistory
): MockEventsTracker {
    const eventsTracker: MockEventsTracker = {
        mockGenerationEventsN: 0,
        successfulGenerationEventsN: 0,
        failedGenerationEventsN: 0,
    };
    testEventLogger.subscribeToLogicEvent(
        mockService.generationFromChatEvent,
        (chatData) => {
            if (mockChat === undefined) {
                expect((chatData as ChatHistory) !== null).toBeTruthy();
            } else {
                expect(chatData as ChatHistory).toEqual(mockChat.chat);
            }
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
    service: LLMService
) {
    const actualRecordsUnwrapped = service.readRequestsLogs().map((record) => {
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
    expect(actualRecordsUnwrapped).toHaveLength(
        expectedRecordsUnwrapped.length
    );
    // if exact error is not expected, ignore it in the actual records
    for (let i = 0; i < expectedRecordsUnwrapped.length; i++) {
        const expected = expectedRecordsUnwrapped[i];
        const actual = actualRecordsUnwrapped[i];
        if (
            expected.status === "FAILED" &&
            actual.status === "FAILED" &&
            expected.error === undefined
        ) {
            actual.error = undefined;
        }
    }
    expect(actualRecordsUnwrapped).toEqual(expectedRecordsUnwrapped);
}

export interface ExpectedGeneratedProof {
    proof: string;
    versionNumber: number;
    proofVersions: ProofVersion[];
    nextVersionCanBeGenerated?: boolean;
    canBeFixed?: Boolean;
}

export function expectGeneratedProof(
    actual: GeneratedProof,
    expected: ExpectedGeneratedProof
) {
    const mockGeneratedProof = actual as MockLLMGeneratedProof;
    expect(mockGeneratedProof.proof()).toEqual(expected.proof);
    expect(mockGeneratedProof.versionNumber()).toEqual(expected.versionNumber);
    expect(mockGeneratedProof.proofVersions).toEqual(expected.proofVersions);
    if (expected.nextVersionCanBeGenerated !== undefined) {
        expect(mockGeneratedProof.nextVersionCanBeGenerated()).toEqual(
            expected.nextVersionCanBeGenerated
        );
    }
    if (expected.canBeFixed !== undefined) {
        expect(mockGeneratedProof.canBeFixed()).toEqual(expected.canBeFixed);
    }
}

export function toProofVersion(
    proof: string,
    diagnostic: string | undefined = undefined
): ProofVersion {
    return { proof: proof, diagnostic: diagnostic };
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
            workerId: 0,
            resolvedWithMockLLMService: true,
        };
        await block(mockService, basicMockParams, testEventLogger);
    } finally {
        mockService.dispose();
    }
}
