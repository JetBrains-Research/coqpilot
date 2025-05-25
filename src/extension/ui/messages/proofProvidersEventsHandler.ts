import {
    ProofProviderRequest,
    ProofProviderRequestFailed,
    ProofProviderRequestSucceeded,
    isProofProviderRequestFailed,
    isProofProviderRequestSucceeded,
} from "../../../proofProviders/impl/commonStructures/proofProviderRequest";
import { ModelParams } from "../../../proofProviders/impl/modelParams";
import { ProofProvider } from "../../../proofProviders/impl/proofProvider";
import { RangoError } from "../../../proofProviders/impl/rango/rangoError";
import {
    ConfigurationError,
    GenerationFailedError,
    RemoteConnectionError,
} from "../../../proofProviders/proofProviderErrors";
import { ProofProvidersStorage } from "../../../proofProviders/proofProvidersStorage";

import { EventLogger } from "../../../logging/eventLogger";
import { SimpleSet } from "../../../utils/collectionUtils/simpleSet";
import { buildErrorCompleteLog } from "../../../utils/errors/errorsUtils";
import { illegalState } from "../../../utils/errors/throwErrors";
import { stringifyAnyValue } from "../../../utils/printers";
import { toSettingName } from "../../settings/settingsNames";
import { openTextDocument } from "../documentOpener";

import {
    EditorMessages,
    showMessageToUser,
    showMessageToUserWithActions,
    showMessageToUserWithSettingsHint,
} from "./editorMessages";

enum ProofProviderAvailablityState {
    AVAILABLE,
    UNAVAILABLE,
}

enum ProofProviderMessagesShownState {
    NO_MESSAGES_SHOWN,
    BECOME_UNAVAILABLE_MESSAGE_SHOWN,
    AGAIN_AVAILABLE_MESSAGE_SHOWN,
}

interface ProofProviderUIState {
    availabilityState: ProofProviderAvailablityState;
    messagesShownState: ProofProviderMessagesShownState;
}

type ProofProviderToUIState = Map<ProofProvider, ProofProviderUIState>;
type ModelsSet = SimpleSet<ModelParams, string>;

export type UnsubscribeFromProofProvidersEventsCallback = () => void;

export function subscribeToHandleProofProvidersEvents(
    proofProviders: ProofProvidersStorage,
    eventLogger: EventLogger
): UnsubscribeFromProofProvidersEventsCallback {
    const proofProviderToUIState = createProofProviderToUIState(proofProviders);
    const seenIncorrectlyConfiguredModels: ModelsSet = new SimpleSet(
        (model: ModelParams) => model.modelId
    );

    const succeededSubscriptionId = eventLogger.subscribeToLogicEvent(
        ProofProvider.requestSucceededEvent,
        reactToRequestSucceededEvent(proofProviderToUIState)
    );
    const failedSubscriptionId = eventLogger.subscribeToLogicEvent(
        ProofProvider.requestFailedEvent,
        reactToRequestFailedEvent(
            proofProviderToUIState,
            seenIncorrectlyConfiguredModels
        )
    );

    return () => {
        eventLogger.unsubscribe(
            ProofProvider.requestSucceededEvent,
            succeededSubscriptionId
        );
        eventLogger.unsubscribe(
            ProofProvider.requestFailedEvent,
            failedSubscriptionId
        );
    };
}

function createProofProviderToUIState(
    proofProviders: ProofProvidersStorage
): ProofProviderToUIState {
    const initialState: ProofProviderUIState = {
        availabilityState: ProofProviderAvailablityState.AVAILABLE,
        messagesShownState: ProofProviderMessagesShownState.NO_MESSAGES_SHOWN,
    };
    return new Map(
        proofProviders.allProofProviders().map((proofProvider) => [
            proofProvider,
            {
                ...initialState,
            },
        ])
    );
}

function reactToRequestSucceededEvent(
    proofProviderToUIState: ProofProviderToUIState
): (data: any) => void {
    return (data: any) => {
        const [requestSucceeded, uiState] =
            parseProofProviderRequestEvent<ProofProviderRequestSucceeded>(
                data,
                isProofProviderRequestSucceeded,
                proofProviderToUIState,
                `data of the ${ProofProvider.requestSucceededEvent} event should be a \`ProofProviderRequestSucceeded\` object`
            );
        if (
            uiState.availabilityState ===
            ProofProviderAvailablityState.UNAVAILABLE
        ) {
            uiState.availabilityState = ProofProviderAvailablityState.AVAILABLE;
            if (
                uiState.messagesShownState ===
                ProofProviderMessagesShownState.BECOME_UNAVAILABLE_MESSAGE_SHOWN
            ) {
                showMessageToUser(
                    EditorMessages.proofProviderIsAvailableAgain(
                        requestSucceeded.proofProvider.name
                    ),
                    "info"
                );
                uiState.messagesShownState =
                    ProofProviderMessagesShownState.AGAIN_AVAILABLE_MESSAGE_SHOWN;
            }
        }
    };
}

function reactToRequestFailedEvent(
    proofProviderToUIState: ProofProviderToUIState,
    seenIncorrectlyConfiguredModels: ModelsSet
): (data: any) => void {
    return (data: any) => {
        const [requestFailed, uiState] =
            parseProofProviderRequestEvent<ProofProviderRequestFailed>(
                data,
                isProofProviderRequestFailed,
                proofProviderToUIState,
                `data of the ${ProofProvider.requestFailedEvent} event should be a \`ProofProviderRequestFailed\` object`
            );

        const proofProviderError = requestFailed.proofProviderError;
        const model = requestFailed.params;
        if (proofProviderError instanceof ConfigurationError) {
            if (seenIncorrectlyConfiguredModels.has(model)) {
                return; // don't show configuration error of the same model to the user twice
            }
            seenIncorrectlyConfiguredModels.add(model);
            showMessageToUserWithSettingsHint(
                EditorMessages.modelConfiguredIncorrectly(
                    model.modelId,
                    proofProviderError.message
                ),
                "error",
                toSettingName(requestFailed.proofProvider.identifier)
            );
            return;
        }
        if (
            !(
                proofProviderError instanceof RemoteConnectionError ||
                proofProviderError instanceof GenerationFailedError
            )
        ) {
            illegalState(
                `\`proofProviderError\` of the received ${ProofProvider.requestFailedEvent} event data `,
                `is expected to be either a \` ConfigurationError\`, \`RemoteConnectionError\`, or \`GenerationFailedError\`, `,
                `but got: ${buildErrorCompleteLog(proofProviderError)}`
            );
        }

        if (
            uiState.availabilityState ===
            ProofProviderAvailablityState.AVAILABLE
        ) {
            uiState.availabilityState =
                ProofProviderAvailablityState.UNAVAILABLE;
            if (
                uiState.messagesShownState ===
                ProofProviderMessagesShownState.NO_MESSAGES_SHOWN
            ) {
                const proofProviderName = requestFailed.proofProvider.name;
                if (proofProviderError instanceof GenerationFailedError) {
                    handleGenerationFailedError(
                        proofProviderName,
                        proofProviderError.cause,
                        requestFailed
                    );
                } else {
                    showMessageToUser(
                        EditorMessages.failedToReachRemoteProofProvider(
                            proofProviderName,
                            proofProviderError.message
                        ),
                        "warning"
                    );
                }
                uiState.messagesShownState =
                    ProofProviderMessagesShownState.BECOME_UNAVAILABLE_MESSAGE_SHOWN;
            }
        }
    };
}

function parseProofProviderRequestEvent<T extends ProofProviderRequest>(
    data: any,
    checkType: (data: any) => data is T,
    proofProviderToUIState: ProofProviderToUIState,
    errorMessage: string
): [T, ProofProviderUIState] {
    if (!checkType(data)) {
        illegalState(`${errorMessage}, but data = ${stringifyAnyValue(data)}`);
    }
    const proofProvider = data.proofProvider;
    const uiState = proofProviderToUIState.get(proofProvider);
    if (uiState === undefined) {
        illegalState(`no UI state for \`${proofProvider.toLogString(false)}\``);
    }
    return [data, uiState];
}

function handleGenerationFailedError(
    proofProviderName: string,
    causeError: Error,
    requestFailed: ProofProviderRequestFailed
) {
    const messageToShow = EditorMessages.proofProviderBecameUnavailable(
        proofProviderName,
        causeError.message,
        requestFailed.proofProvider.estimateTimeToBecomeAvailable()
    );
    const logsFileToOpen =
        causeError instanceof RangoError ? causeError.logsPath : undefined;
    if (logsFileToOpen !== undefined) {
        showMessageToUserWithActions(messageToShow, "warning", {
            choiceItem: "Open logs",
            callback: () => openTextDocument(logsFileToOpen),
        });
    } else {
        showMessageToUser(messageToShow, "warning");
    }
}
