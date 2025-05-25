import { expect } from "earl";

import {
    AnalyzedChatHistory,
    ChatHistory,
} from "../../../proofProviders/impl/commonStructures/chat";
import {
    ProofProviderRequestFailed,
    ProofProviderRequestSucceeded,
    isProofProviderRequestFailed,
    isProofProviderRequestSucceeded,
} from "../../../proofProviders/impl/commonStructures/proofProviderRequest";
import { ProofProvider } from "../../../proofProviders/impl/proofProvider";
import { ProofProviderError } from "../../../proofProviders/proofProviderErrors";

import { EventLogger } from "../../../logging/eventLogger";

import { MockService } from "./mockService";

export interface EventsTracker {
    successfulRequestEventsN: number;
    failedRequestEventsN: number;
}

export function subscribeToTrackEvents<ProofProviderType extends ProofProvider>(
    testEventLogger: EventLogger,
    expectedService: ProofProviderType,
    expectedModelId: string,
    expectedError?: ProofProviderError
): EventsTracker {
    const eventsTracker: EventsTracker = {
        successfulRequestEventsN: 0,
        failedRequestEventsN: 0,
    };
    subscribeToLogicEvents(
        eventsTracker,
        testEventLogger,
        expectedService,
        expectedModelId,
        expectedError
    );
    return eventsTracker;
}

export interface MockEventsTracker extends EventsTracker {
    mockEventsN: number;
}

export function subscribeToTrackMockEvents(
    testEventLogger: EventLogger,
    expectedMockService: MockService,
    expectedModelId: string,
    expectedMockChat?: AnalyzedChatHistory,
    expectedError?: ProofProviderError
): MockEventsTracker {
    const eventsTracker: MockEventsTracker = {
        mockEventsN: 0,
        successfulRequestEventsN: 0,
        failedRequestEventsN: 0,
    };
    testEventLogger.subscribeToLogicEvent(
        MockService.generationFromChatEvent,
        (chatData) => {
            if (expectedMockChat === undefined) {
                expect(chatData).toBeTruthy();
            } else {
                expect(chatData as ChatHistory).toEqual(expectedMockChat.chat);
            }
            eventsTracker.mockEventsN += 1;
        }
    );
    subscribeToLogicEvents(
        eventsTracker,
        testEventLogger,
        expectedMockService,
        expectedModelId,
        expectedError
    );
    return eventsTracker;
}

function subscribeToLogicEvents<ProofProviderType extends ProofProvider>(
    eventsTracker: EventsTracker,
    testEventLogger: EventLogger,
    expectedService: ProofProviderType,
    expectedModelId: string,
    expectedError?: ProofProviderError
) {
    testEventLogger.subscribeToLogicEvent(
        ProofProvider.requestSucceededEvent,
        (data) => {
            expect(isProofProviderRequestSucceeded(data)).toBeTruthy();
            const requestSucceeded = data as ProofProviderRequestSucceeded;

            expect(requestSucceeded.proofProvider).toEqual(expectedService);
            expect(requestSucceeded.params.modelId).toEqual(expectedModelId);
            eventsTracker.successfulRequestEventsN += 1;
        }
    );
    testEventLogger.subscribeToLogicEvent(
        ProofProvider.requestFailedEvent,
        (data) => {
            expect(isProofProviderRequestFailed(data)).toBeTruthy();
            const requestFailed = data as ProofProviderRequestFailed;

            expect(requestFailed.proofProvider).toEqual(expectedService);
            expect(requestFailed.params.modelId).toEqual(expectedModelId);
            if (expectedError !== undefined) {
                expect(requestFailed.proofProviderError).toEqual(expectedError);
            }
            eventsTracker.failedRequestEventsN += 1;
        }
    );
}
