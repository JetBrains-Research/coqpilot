import { LLMServices } from "../llm/llmServices";
import { LLMService } from "../llm/llmServices/llmService";
import { Time } from "../llm/llmServices/utils/time";

import { EventLogger } from "../logging/eventLogger";

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
    const generationFailedSubscriptionId = eventLogger.subscribeToLogicEvent(
        LLMService.generationFailedEvent,
        reactToGenerationFailedEvent(llmServiceToUIState)
    );
    const generationSucceededSubscriptionId = eventLogger.subscribeToLogicEvent(
        LLMService.generationSucceededEvent,
        reactToGenerationSucceededEvent(llmServiceToUIState)
    );
    return () => {
        eventLogger.unsubscribe(
            LLMService.generationFailedEvent,
            generationFailedSubscriptionId
        );
        eventLogger.unsubscribe(
            LLMService.generationSucceededEvent,
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

function reactToGenerationFailedEvent(
    llmServiceToUIState: LLMServiceToUIState
): (data: any) => void {
    return (data: any) => {
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
                const formattedExpectedTime = formatTimeToUIString(
                    llmService.estimateTimeToBecomeAvailable()
                );
                const becameUnavailableMessage = `\`${serviceName}\` became unavailable for this generation.`;
                const tryAgainMessage = `If you want to use it, try again in ~ ${formattedExpectedTime}.`;
                showMessageToUser(
                    `${becameUnavailableMessage} ${tryAgainMessage}`,
                    "warning"
                );
            }
        }
    };
}

function reactToGenerationSucceededEvent(
    llmServiceToUIState: LLMServiceToUIState
): (data: any) => void {
    return (data: any) => {
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
}

function parseLLMServiceLogicEventData(
    data: any,
    llmServiceToUIState: LLMServiceToUIState
): [LLMService, LLMServiceUIState] {
    const llmService = data as LLMService;
    if (llmService === null) {
        throw Error("data of the generation event should be a LLMService");
    }
    const serviceName = llmService.serviceName;
    const uiState = llmServiceToUIState[serviceName];
    if (uiState === undefined) {
        throw Error(`no UI state for \`${serviceName}\``);
    }
    return [llmService, uiState];
}

function formatTimeToUIString(time: Time): string {
    const days = formatTimeItem(time.days, "day");
    const hours = formatTimeItem(time.hours, "hour");
    const minutes = formatTimeItem(time.minutes, "minute");
    const seconds = formatTimeItem(time.seconds, "second");

    if (time.days === 0) {
        if (time.hours === 0) {
            if (time.minutes === 0) {
                return `${seconds}`;
            } else {
                return `${minutes}, ${seconds}`;
            }
        } else {
            return `${hours}, ${minutes}`;
        }
    } else {
        return `${days}, ${hours}`;
    }
}

function formatTimeItem(value: number, name: string): string {
    const suffix = value === 1 ? "" : "s";
    return `${value} ${name}${suffix}`;
}
