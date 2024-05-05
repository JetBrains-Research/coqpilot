import { LLMServiceError } from "../llm/llmServiceErrors";
import { LLMServices } from "../llm/llmServices";
import { LLMService } from "../llm/llmServices/llmService";
import { ModelParams } from "../llm/llmServices/modelParams";
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

class FailedModelsSet {
    private readonly modelAsJSONIsFailed: Map<string, boolean> = new Map();

    add(model: ModelParams) {
        this.modelAsJSONIsFailed.set(JSON.stringify(model), true);
    }

    has(model: ModelParams) {
        this.modelAsJSONIsFailed.has(JSON.stringify(model));
    }
}

export type UnsubscribeFromLLMServicesUIEventsCallback = () => void;

export function subscribeToLLMServicesUIEvents(
    llmServices: LLMServices,
    eventLogger: EventLogger
): UnsubscribeFromLLMServicesUIEventsCallback {
    const llmServiceToUIState: LLMServiceToUIState =
        createLLMServiceToUIState(llmServices);
    const failedModels = new FailedModelsSet();

    const succeededSubscriptionId = eventLogger.subscribeToLogicEvent(
        LLMService.generationRequestSucceededEvent,
        reactToGenerationRequestSucceededEvent(llmServiceToUIState)
    );
    const failedSubscriptionId = eventLogger.subscribeToLogicEvent(
        LLMService.generationRequestFailedEvent,
        reactToGenerationRequestFailedEvent(llmServiceToUIState, failedModels)
    );
    return () => {
        eventLogger.unsubscribe(
            LLMService.generationRequestSucceededEvent,
            succeededSubscriptionId
        );
        eventLogger.unsubscribe(
            LLMService.generationRequestFailedEvent,
            failedSubscriptionId
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

function reactToGenerationRequestSucceededEvent(
    llmServiceToUIState: LLMServiceToUIState
): (data: any) => void {
    return (data: any) => {
        const [llmService, _, uiState] = parseLLMServiceLogicEventData(
            data,
            false,
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

function reactToGenerationRequestFailedEvent(
    llmServiceToUIState: LLMServiceToUIState,
    _failedModels: FailedModelsSet
): (data: any) => void {
    return (data: any) => {
        const [llmService, _, uiState] = parseLLMServiceLogicEventData(
            data,
            true,
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

// TODO: pass and parse model
// use Map instead of primitive map
function parseLLMServiceLogicEventData(
    data: any,
    isFailure: boolean,
    llmServiceToUIState: LLMServiceToUIState
): [LLMService, LLMServiceError | undefined, LLMServiceUIState] {
    let llmService: LLMService | undefined = undefined;
    let llmServiceError: LLMServiceError | undefined = undefined;
    if (isFailure) {
        const llmServiceAndError = data as [LLMService, LLMServiceError];
        if (llmServiceAndError === null) {
            throw Error(
                `data of the failed generation request event should be a \`[LLMService, LLMServiceError]\`, data = \`${data}\``
            );
        }
        [llmService, llmServiceError] = llmServiceAndError;
    } else {
        llmService = data as LLMService;
        if (llmService === null) {
            throw Error(
                `data of the succeeded generation request event should be a \`LLMService\`, data = \`${data}\``
            );
        }
    }

    const serviceName = llmService.serviceName;
    const uiState = llmServiceToUIState[serviceName];
    if (uiState === undefined) {
        throw Error(`no UI state for \`${serviceName}\``);
    }
    return [llmService, llmServiceError, uiState];
}

function formatTimeToUIString(time: Time): string {
    const days = formatTimeItem(time.days, "day");
    const hours = formatTimeItem(time.hours, "hour");
    const minutes = formatTimeItem(time.minutes, "minute");
    const seconds = formatTimeItem(time.seconds, "second");

    // TODO: for algorithm
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
