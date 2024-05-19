import {
    ConfigurationError,
    GenerationFailedError,
    RemoteConnectionError,
} from "../llm/llmServiceErrors";
import { LLMServices, asLLMServices } from "../llm/llmServices";
import {
    LLMServiceImpl,
    LLMServiceRequest,
    LLMServiceRequestFailed,
    LLMServiceRequestSucceeded,
} from "../llm/llmServices/llmService";
import { ModelParams } from "../llm/llmServices/modelParams";
import { Time } from "../llm/llmServices/utils/time";

import { EventLogger } from "../logging/eventLogger";
import { SimpleSet } from "../utils/simpleSet";

import { EditorMessages, showMessageToUser } from "./editorMessages";
import {
    showMessageToUserWithSettingsHint,
    toSettingName,
} from "./settingsValidationError";

enum LLMServiceAvailablityState {
    AVAILABLE,
    UNAVAILABLE,
}

enum LLMServiceMessagesShownState {
    NO_MESSAGES_SHOWN,
    BECOME_UNAVAILABLE_MESSAGE_SHOWN,
    AGAIN_AVAILABLE_MESSAGE_SHOWN,
}

interface LLMServiceUIState {
    availabilityState: LLMServiceAvailablityState;
    messagesShownState: LLMServiceMessagesShownState;
}

type LLMServiceToUIState = Map<string, LLMServiceUIState>;
type ModelsSet = SimpleSet<ModelParams, string>;

export type UnsubscribeFromLLMServicesEventsCallback = () => void;

export function subscribeToHandleLLMServicesEvents(
    llmServices: LLMServices,
    eventLogger: EventLogger
): UnsubscribeFromLLMServicesEventsCallback {
    const llmServiceToUIState = createLLMServiceToUIState(llmServices);
    const seenIncorrectlyConfiguredModels: ModelsSet = new SimpleSet(
        (model: ModelParams) => model.modelId
    );

    const succeededSubscriptionId = eventLogger.subscribeToLogicEvent(
        LLMServiceImpl.requestSucceededEvent,
        reactToRequestSucceededEvent(llmServiceToUIState)
    );
    const failedSubscriptionId = eventLogger.subscribeToLogicEvent(
        LLMServiceImpl.requestFailedEvent,
        reactToRequestFailedEvent(
            llmServiceToUIState,
            seenIncorrectlyConfiguredModels
        )
    );

    return () => {
        eventLogger.unsubscribe(
            LLMServiceImpl.requestSucceededEvent,
            succeededSubscriptionId
        );
        eventLogger.unsubscribe(
            LLMServiceImpl.requestFailedEvent,
            failedSubscriptionId
        );
    };
}

function createLLMServiceToUIState(
    llmServices: LLMServices
): LLMServiceToUIState {
    const initialState: LLMServiceUIState = {
        availabilityState: LLMServiceAvailablityState.AVAILABLE,
        messagesShownState: LLMServiceMessagesShownState.NO_MESSAGES_SHOWN,
    };
    return new Map(
        asLLMServices(llmServices).map((llmService) => [
            llmService.serviceName,
            {
                ...initialState,
            },
        ])
    );
}

function reactToRequestSucceededEvent(
    llmServiceToUIState: LLMServiceToUIState
): (data: any) => void {
    return (data: any) => {
        const [requestSucceeded, uiState] =
            parseLLMServiceRequestEvent<LLMServiceRequestSucceeded>(
                data,
                llmServiceToUIState,
                `data of the ${LLMServiceImpl.requestSucceededEvent} event should be a \`LLMServiceRequestSucceeded\` object`
            );
        if (
            uiState.availabilityState === LLMServiceAvailablityState.UNAVAILABLE
        ) {
            uiState.availabilityState = LLMServiceAvailablityState.AVAILABLE;
            if (
                uiState.messagesShownState ===
                LLMServiceMessagesShownState.BECOME_UNAVAILABLE_MESSAGE_SHOWN
            ) {
                showMessageToUser(
                    `\`${requestSucceeded.llmService.serviceName}\` is available again!`,
                    "info"
                );
                uiState.messagesShownState =
                    LLMServiceMessagesShownState.AGAIN_AVAILABLE_MESSAGE_SHOWN;
            }
        }
    };
}

function reactToRequestFailedEvent(
    llmServiceToUIState: LLMServiceToUIState,
    seenIncorrectlyConfiguredModels: ModelsSet
): (data: any) => void {
    return (data: any) => {
        const [requestFailed, uiState] =
            parseLLMServiceRequestEvent<LLMServiceRequestFailed>(
                data,
                llmServiceToUIState,
                `data of the ${LLMServiceImpl.requestFailedEvent} event should be a \`LLMServiceRequestFailed\` object`
            );

        const llmServiceError = requestFailed.llmServiceError;
        const model = requestFailed.params;
        if (llmServiceError instanceof ConfigurationError) {
            if (seenIncorrectlyConfiguredModels.has(model)) {
                return; // don't show configuration error of the same model to the user twice
            }
            seenIncorrectlyConfiguredModels.add(model);
            showMessageToUserWithSettingsHint(
                EditorMessages.modelConfiguredIncorrectly(
                    model.modelId,
                    llmServiceError.message
                ),
                "error",
                toSettingName(requestFailed.llmService)
            );
            return;
        }
        if (
            !(
                llmServiceError instanceof RemoteConnectionError ||
                llmServiceError instanceof GenerationFailedError
            )
        ) {
            throw Error(
                `\`llmServiceError\` of the received ${LLMServiceImpl.requestFailedEvent} event data is expected to be either a \` ConfigurationError\`, \`RemoteConnectionError\`, or \`GenerationFailedError\`, but got: "${llmServiceError}"`
            );
        }

        if (
            uiState.availabilityState === LLMServiceAvailablityState.AVAILABLE
        ) {
            uiState.availabilityState = LLMServiceAvailablityState.UNAVAILABLE;
            if (
                uiState.messagesShownState ===
                LLMServiceMessagesShownState.NO_MESSAGES_SHOWN
            ) {
                if (llmServiceError instanceof GenerationFailedError) {
                    const formattedExpectedTime = formatTimeToUIString(
                        requestFailed.llmService.estimateTimeToBecomeAvailable()
                    );
                    const becameUnavailableMessage = `\`${requestFailed.llmService.serviceName}\` became unavailable for this generation.`;
                    const errorMessage = llmServiceError.cause.message;
                    const tryAgainMessage = `If you want to use it, try again in ~ ${formattedExpectedTime}. Caused by error: "${errorMessage}".`;
                    showMessageToUser(
                        `${becameUnavailableMessage} ${tryAgainMessage}`,
                        "warning"
                    );
                } else {
                    const serviceFailureMessage = `\`${requestFailed.llmService.serviceName}\` became unavailable for this generation: ${llmServiceError.message}.`;
                    const tryAgainMessage = `Check your internet connection and try again.`;
                    showMessageToUser(
                        `${serviceFailureMessage} ${tryAgainMessage}`,
                        "warning"
                    );
                }
                uiState.messagesShownState =
                    LLMServiceMessagesShownState.BECOME_UNAVAILABLE_MESSAGE_SHOWN;
            }
        }
    };
}

function parseLLMServiceRequestEvent<T extends LLMServiceRequest>(
    data: any,
    llmServiceToUIState: LLMServiceToUIState,
    errorMessage: string
): [T, LLMServiceUIState] {
    const request = data as T;
    if (request === null) {
        throw Error(`${errorMessage}, but data = \`${data}\``);
    }
    const serviceName = request.llmService.serviceName;
    const uiState = llmServiceToUIState.get(serviceName);
    if (uiState === undefined) {
        throw Error(`no UI state for \`${serviceName}\``);
    }
    return [request, uiState];
}

function formatTimeToUIString(time: Time): string {
    const orderedTimeItems: [number, string][] = [
        [time.days, "day"],
        [time.hours, "hour"],
        [time.minutes, "minute"],
        [time.seconds, "second"],
    ].map(([value, name]) => [
        value as number,
        formatTimeItem(value as number, name as string),
    ]);
    const itemsN = orderedTimeItems.length;

    for (let i = 0; i < itemsN; i++) {
        const [value, formattedItem] = orderedTimeItems[i];
        if (value !== 0) {
            const nextFormattedItem =
                i === itemsN - 1 ? "" : `, ${orderedTimeItems[i + 1][1]}`;
            return `${formattedItem}${nextFormattedItem}`;
        }
    }
    const zeroSeconds = orderedTimeItems[3][1];
    return `${zeroSeconds}`;
}

function formatTimeItem(value: number, name: string): string {
    const suffix = value === 1 ? "" : "s";
    return `${value} ${name}${suffix}`;
}
