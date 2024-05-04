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
    targetService: LLMService
): EventsTracker {
    const eventsTracker: EventsTracker = {
        successfulGenerationEventsN: 0,
        failedGenerationEventsN: 0,
    };
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
            const serviceAndError = data as [LLMService, LLMServiceError];
            expect(serviceAndError).toBeTruthy();
            expect(serviceAndError[0]).toEqual(targetService);
            eventsTracker.failedGenerationEventsN += 1;
        }
    );
    return eventsTracker;
}

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
    testEventLogger.subscribeToLogicEvent(
        LLMService.generationRequestSucceededEvent,
        (service) => {
            expect(service as MockLLMService).toEqual(mockService);
            eventsTracker.successfulGenerationEventsN += 1;
        }
    );
    testEventLogger.subscribeToLogicEvent(
        LLMService.generationRequestFailedEvent,
        (data) => {
            const serviceAndError = data as [MockLLMService, LLMServiceError];
            expect(serviceAndError).toBeTruthy();
            expect(serviceAndError[0]).toEqual(mockService);
            eventsTracker.failedGenerationEventsN += 1;
        }
    );
    return eventsTracker;
}
