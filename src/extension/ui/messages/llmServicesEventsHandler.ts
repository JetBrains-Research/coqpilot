import {
    ConfigurationError,
    GenerationFailedError,
    RemoteConnectionError,
} from "../../../llm/llmServiceErrors";
import { LLMServices, asLLMServices } from "../../../llm/llmServices";
import {
    LLMServiceRequest,
    LLMServiceRequestFailed,
    LLMServiceRequestSucceeded,
    isLLMServiceRequestFailed,
    isLLMServiceRequestSucceeded,
} from "../../../llm/llmServices/commonStructures/llmServiceRequest";
import { LLMServiceImpl } from "../../../llm/llmServices/llmService";
import { ModelParams } from "../../../llm/llmServices/modelParams";

import { EventLogger } from "../../../logging/eventLogger";
import { buildErrorCompleteLog } from "../../../utils/errorsUtils";
import { stringifyAnyValue } from "../../../utils/printers";
import { SimpleSet } from "../../../utils/simpleSet";
import { illegalState } from "../../../utils/throwErrors";
import { toSettingName } from "../../settings/settingsValidationError";

import {
    EditorMessages,
    showMessageToUser,
    showMessageToUserWithSettingsHint,
} from "./editorMessages";

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
                isLLMServiceRequestSucceeded,
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
                    EditorMessages.serviceIsAvailableAgain(
                        requestSucceeded.llmService.serviceName
                    ),
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
                isLLMServiceRequestFailed,
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
            illegalState(
                `\`llmServiceError\` of the received ${LLMServiceImpl.requestFailedEvent} event data `,
                `is expected to be either a \` ConfigurationError\`, \`RemoteConnectionError\`, or \`GenerationFailedError\`, `,
                `but got: ${buildErrorCompleteLog(llmServiceError)}`
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
                const serviceName = requestFailed.llmService.serviceName;
                if (llmServiceError instanceof GenerationFailedError) {
                    showMessageToUser(
                        EditorMessages.serviceBecameUnavailable(
                            serviceName,
                            llmServiceError.cause.message,
                            requestFailed.llmService.estimateTimeToBecomeAvailable()
                        ),
                        "warning"
                    );
                } else {
                    showMessageToUser(
                        EditorMessages.failedToReachRemoteService(
                            serviceName,
                            llmServiceError.message
                        ),
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
    checkType: (data: any) => data is T,
    llmServiceToUIState: LLMServiceToUIState,
    errorMessage: string
): [T, LLMServiceUIState] {
    if (!checkType(data)) {
        illegalState(`${errorMessage}, but data = ${stringifyAnyValue(data)}`);
    }
    const serviceName = data.llmService.serviceName;
    const uiState = llmServiceToUIState.get(serviceName);
    if (uiState === undefined) {
        illegalState(`no UI state for \`${serviceName}\``);
    }
    return [data, uiState];
}
