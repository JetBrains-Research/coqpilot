import {
    ConfigurationError,
    GenerationFailedError,
} from "../llm/llmServiceErrors";
import {
    LLMServices,
    asLLMServices,
    switchByLLMServiceType,
} from "../llm/llmServices";
import {
    LLMService,
    LLMServiceRequest,
    LLMServiceRequestFailed,
    LLMServiceRequestSucceeded,
} from "../llm/llmServices/llmService";
import { ModelParams } from "../llm/llmServices/modelParams";
import { Time } from "../llm/llmServices/utils/time";

import { EventLogger } from "../logging/eventLogger";
import { SimpleSet } from "../utils/simpleSet";

import { pluginId } from "./coqPilot";
import { showMessageToUser } from "./editorMessages";
import { showMessageToUserWithSettingsHint } from "./settingsValidationError";

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
        LLMService.requestSucceededEvent,
        reactToRequestSucceededEvent(llmServiceToUIState)
    );
    const failedSubscriptionId = eventLogger.subscribeToLogicEvent(
        LLMService.requestFailedEvent,
        reactToRequestFailedEvent(
            llmServiceToUIState,
            seenIncorrectlyConfiguredModels
        )
    );

    return () => {
        eventLogger.unsubscribe(
            LLMService.requestSucceededEvent,
            succeededSubscriptionId
        );
        eventLogger.unsubscribe(
            LLMService.requestFailedEvent,
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
                `data of the ${LLMService.requestSucceededEvent} event should be a \`LLMServiceRequestSucceeded\` object`
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
                `data of the ${LLMService.requestFailedEvent} event should be a \`LLMServiceRequestFailed\` object`
            );

        const llmServiceError = requestFailed.llmServiceError;
        const model = requestFailed.params;
        if (llmServiceError instanceof ConfigurationError) {
            if (seenIncorrectlyConfiguredModels.has(model)) {
                return; // don't show configuration error of the same model to the user twice
            }
            seenIncorrectlyConfiguredModels.add(model);
            showMessageToUserWithSettingsHint(
                `Model "${model.modelId}" is configured incorrectly: ${llmServiceError.message}. Thus, "${model.modelId}" will be skipped for this run. Please fix the model's configuration in the settings.`,
                "error",
                toSettingName(requestFailed.llmService)
            );
            return;
        }
        if (!(llmServiceError instanceof GenerationFailedError)) {
            throw Error(
                `\`llmServiceError\` of the received ${LLMService.requestFailedEvent} event data is expected to be either a \` ConfigurationError\` or \`GenerationFailedError\`, but got: "${llmServiceError}"`
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

function toSettingName(llmService: LLMService): string {
    const serviceNameInSettings = switchByLLMServiceType(
        llmService,
        () => "predefinedProofs",
        () => "openAi",
        () => "grazie",
        () => "lmStudio"
    );
    return `${pluginId}.${serviceNameInSettings}ModelsParameters`;
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
