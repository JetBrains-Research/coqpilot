import { expect } from "earl";

import { LLMServiceError } from "../../../llm/llmServiceErrors";
import {
    AnalyzedChatHistory,
    ChatHistory,
} from "../../../llm/llmServices/chat";
import { LLMService } from "../../../llm/llmServices/llmService";

import { EventLogger } from "../../../logging/eventLogger";

import { MockLLMService } from "./mockLLMService";

export interface EventsTracker {
    successfulGenerationEventsN: number;
    failedGenerationEventsN: number;
}

export function subscribeToTrackEvents(
    testEventLogger: EventLogger,
    targetService: LLMService,
    expectedError?: LLMServiceError
): EventsTracker {
    const eventsTracker: EventsTracker = {
        successfulGenerationEventsN: 0,
        failedGenerationEventsN: 0,
    };
    subscribeToLogicEvents(
        eventsTracker,
        testEventLogger,
        targetService,
        expectedError
    );
    return eventsTracker;
}

export interface MockEventsTracker extends EventsTracker {
    mockGenerationEventsN: number;
}

export function subscribeToTrackMockEvents(
    testEventLogger: EventLogger,
    mockService: MockLLMService,
    mockChat?: AnalyzedChatHistory,
    expectedError?: LLMServiceError
): MockEventsTracker {
    const eventsTracker: MockEventsTracker = {
        mockGenerationEventsN: 0,
        successfulGenerationEventsN: 0,
        failedGenerationEventsN: 0,
    };
    testEventLogger.subscribeToLogicEvent(
        MockLLMService.generationFromChatEvent,
        (chatData) => {
            if (mockChat === undefined) {
                expect((chatData as ChatHistory) !== null).toBeTruthy();
            } else {
                expect(chatData as ChatHistory).toEqual(mockChat.chat);
            }
            eventsTracker.mockGenerationEventsN += 1;
        }
    );
    subscribeToLogicEvents(
        eventsTracker,
        testEventLogger,
        mockService,
        expectedError
    );
    return eventsTracker;
}

function subscribeToLogicEvents<T>(
    eventsTracker: EventsTracker,
    testEventLogger: EventLogger,
    targetService: T,
    expectedError?: LLMServiceError
) {
    testEventLogger.subscribeToLogicEvent(
        LLMService.generationRequestSucceededEvent,
        (service) => {
            expect(service).toEqual(targetService);
            eventsTracker.successfulGenerationEventsN += 1;
        }
    );
    testEventLogger.subscribeToLogicEvent(
        LLMService.generationRequestFailedEvent,
        (data) => {
            checkRequestFailedEventData(data, targetService, expectedError);
            eventsTracker.failedGenerationEventsN += 1;
        }
    );
}

function checkRequestFailedEventData<T>(
    data: any,
    targetService: T,
    expectedError?: LLMServiceError
) {
    const serviceAndError = data as [T, LLMServiceError];
    expect(serviceAndError).toBeTruthy();
    expect(serviceAndError[0]).toEqual(targetService);
    if (expectedError !== undefined) {
        expect(serviceAndError[1]).toEqual(expectedError);
    }
}
