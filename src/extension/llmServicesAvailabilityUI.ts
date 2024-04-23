import { LLMServices } from "../llm/llmServices";
import { LLMService } from "../llm/llmServices/llmService";

import { EventLogger, SubscriptionId } from "../logging/eventLogger";

import { showMessageToUser } from "./editorMessages";

/* eslint-disable @typescript-eslint/naming-convention */
enum LLMServiceAvailablityState {
    AVAILABLE = "AVAILABLE",
    UNAVAILABLE = "UNAVAILABLE",
}

/* eslint-disable @typescript-eslint/naming-convention */
enum LLMServiceMessagesShownState {
    NO_MESSAGES_SHOWN = "NO_MESSAGES_SHOWN",
    BECOME_UNAVAILABLE_MESSAGE_SHOWN = "BECOME_UNAVAILABLE_MESSAGE_SHOWN",
    AGAIN_AVAILABLE_MESSAGE_SHOWN = "AGAIN_AVAILABLE_MESSAGE_SHOWN",
}

interface LLMServiceUIState {
    availabilityState: LLMServiceAvailablityState;
    messagesShownState: LLMServiceMessagesShownState;
}

type LLMServiceToUIState = {
    [key: string]: LLMServiceUIState;
};

export type UnsubscribeFromLLMServicesUIEventsCallback = () => void;

export function subscribeToLLMServicesUIEvents(
    llmServices: LLMServices,
    eventLogger: EventLogger
): UnsubscribeFromLLMServicesUIEventsCallback {
    const llmServiceToUIState: LLMServiceToUIState =
        createLLMServiceToUIState(llmServices);
    const generationFailedSubscriptionId =
        subscribeToGenerationFromChatFailedEvent(
            llmServiceToUIState,
            eventLogger
        );
    const generationSucceededSubscriptionId =
        subscribeToGenerationFromChatSucceededEvent(
            llmServiceToUIState,
            eventLogger
        );
    return () => {
        eventLogger.unsubscribe(
            LLMService.generationFromChatFailedEvent,
            generationFailedSubscriptionId
        );
        eventLogger.unsubscribe(
            LLMService.generationFromChatSucceededEvent,
            generationSucceededSubscriptionId
        );
    };
}

function createLLMServiceToUIState(
    llmServices: LLMServices
): LLMServiceToUIState {
    return {
        [llmServices.openAiService.serviceName]: {
            availabilityState: LLMServiceAvailablityState.AVAILABLE,
            messagesShownState: LLMServiceMessagesShownState.NO_MESSAGES_SHOWN,
        },
        [llmServices.grazieService.serviceName]: {
            availabilityState: LLMServiceAvailablityState.AVAILABLE,
            messagesShownState: LLMServiceMessagesShownState.NO_MESSAGES_SHOWN,
        },
        [llmServices.predefinedProofsService.serviceName]: {
            availabilityState: LLMServiceAvailablityState.AVAILABLE,
            messagesShownState: LLMServiceMessagesShownState.NO_MESSAGES_SHOWN,
        },
        [llmServices.lmStudioService.serviceName]: {
            availabilityState: LLMServiceAvailablityState.AVAILABLE,
            messagesShownState: LLMServiceMessagesShownState.NO_MESSAGES_SHOWN,
        },
    };
}

function subscribeToGenerationFromChatFailedEvent(
    llmServiceToUIState: LLMServiceToUIState,
    eventLogger: EventLogger
): SubscriptionId {
    const callback = (data: any) => {
        const [llmService, uiState] = parseLLMServiceLogicEventData(
            data,
            llmServiceToUIState
        );
        const serviceName = llmService.serviceName;
        if (
            uiState.availabilityState === LLMServiceAvailablityState.AVAILABLE
        ) {
            llmServiceToUIState[serviceName].availabilityState =
                LLMServiceAvailablityState.UNAVAILABLE;
            if (
                uiState.messagesShownState ===
                LLMServiceMessagesShownState.NO_MESSAGES_SHOWN
            ) {
                showMessageToUser(
                    `\`${serviceName}\` became unavailable for this generation. If you want to use it, try again later.`,
                    "warning"
                );
                // TODO: estimate time
            }
        }
    };
    return eventLogger.subscribeToLogicEvent(
        LLMService.generationFromChatFailedEvent,
        callback
    );
}

function subscribeToGenerationFromChatSucceededEvent(
    llmServiceToUIState: LLMServiceToUIState,
    eventLogger: EventLogger
): SubscriptionId {
    const callback = (data: any) => {
        const [llmService, uiState] = parseLLMServiceLogicEventData(
            data,
            llmServiceToUIState
        );
        const serviceName = llmService.serviceName;
        if (
            uiState.availabilityState === LLMServiceAvailablityState.UNAVAILABLE
        ) {
            llmServiceToUIState[serviceName].availabilityState =
                LLMServiceAvailablityState.AVAILABLE;
            if (
                uiState.messagesShownState ===
                LLMServiceMessagesShownState.BECOME_UNAVAILABLE_MESSAGE_SHOWN
            ) {
                showMessageToUser(
                    `\`${serviceName}\` is available again!`,
                    "info"
                );
            }
        }
    };
    return eventLogger.subscribeToLogicEvent(
        LLMService.generationFromChatSucceededEvent,
        callback
    );
}

function parseLLMServiceLogicEventData(
    data: any,
    llmServiceToUIState: LLMServiceToUIState
): [LLMService, LLMServiceUIState] {
    const llmService = data as LLMService;
    if (llmService === null) {
        throw Error(
            "data of the `generationFromChatFailedEvent` should be a LLMService"
        );
    }
    const serviceName = llmService.serviceName;
    const uiState = llmServiceToUIState[serviceName];
    if (uiState === undefined) {
        throw Error(`no UI state for \`${serviceName}\``);
    }
    return [llmService, uiState];
}
