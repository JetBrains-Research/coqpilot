import Ajv, { JSONSchemaType } from "ajv";
import * as fs from "fs";
import * as path from "path";
import {
    ExtensionContext,
    ProgressLocation,
    TextEditor,
    WorkspaceConfiguration,
    commands,
    extensions,
    window,
    workspace,
} from "vscode";

import { LLMServices } from "../llm/llmServices";
import { GrazieService } from "../llm/llmServices/grazie/grazieService";
import { LLMService } from "../llm/llmServices/llmService";
import { LMStudioService } from "../llm/llmServices/lmStudio/lmStudioService";
import { OpenAiService } from "../llm/llmServices/openai/openAiService";
import { PredefinedProofsService } from "../llm/llmServices/predefinedProofs/predefinedProofsService";
import {
    GrazieUserModelParams,
    LMStudioUserModelParams,
    OpenAiUserModelParams,
    PredefinedProofsUserModelParams,
    UserModelsParams,
    grazieUserModelParamsSchema,
    lmStudioUserModelParamsSchema,
    openAiUserModelParamsSchema,
    predefinedProofsUserModelParamsSchema,
} from "../llm/userModelParams";

import { CoqLspClient } from "../coqLsp/coqLspClient";
import { CoqLspConfig } from "../coqLsp/coqLspConfig";

import { generateCompletion } from "../core/completionGenerator";
import {
    FailureGenerationResult,
    FailureGenerationStatus,
    SuccessGenerationResult,
} from "../core/completionGenerator";
import {
    CompletionContext,
    ProcessEnvironment,
    SourceFileEnvironment,
} from "../core/completionGenerator";
import { ContextTheoremsRanker } from "../core/contextTheoremRanker/contextTheoremsRanker";
import { DistanceContextTheoremsRanker } from "../core/contextTheoremRanker/distanceContextTheoremsRanker";
import { RandomContextTheoremsRanker } from "../core/contextTheoremRanker/randomContextTheoremsRanker";
import { CoqProofChecker } from "../core/coqProofChecker";
import { inspectSourceFile } from "../core/inspectSourceFile";

import { ProofStep } from "../coqParser/parsedTypes";
import { EventLogger, Severity, SubscriptionId } from "../logging/eventLogger";
import { Uri } from "../utils/uri";

import {
    deleteTextFromRange,
    highlightTextInEditor,
    insertCompletion,
} from "./documentEditor";
import {
    EditorMessages,
    showApiKeyNotProvidedMessage,
    showMessageToUser,
    suggestAddingAuxFilesToGitignore,
} from "./editorMessages";
import {
    positionInRange,
    toVSCodePosition,
    toVSCodeRange,
} from "./positionRangeUtils";
import { cleanAuxFiles, hideAuxFiles } from "./tmpFilesCleanup";
import VSCodeLogWriter from "./vscodeLogWriter";

export const pluginId = "coqpilot";

export class GlobalExtensionState {
    public readonly eventLogger: EventLogger = new EventLogger();
    public readonly logWriter: VSCodeLogWriter = new VSCodeLogWriter(
        this.eventLogger,
        this.parseLoggingVerbosity(workspace.getConfiguration(pluginId))
    );

    private readonly llmServicesLogsDirName = "llm-services-logs/";
    // TODO: hide this directory (?) + test
    public readonly llmServicesLogsDir = path.join(
        extensions.getExtension(pluginId)!.extensionPath,
        this.llmServicesLogsDirName
    );

    public readonly llmServices: LLMServices = {
        openAiService: new OpenAiService(
            `${this.llmServicesLogsDir}openai-logs.txt`,
            this.eventLogger
        ),
        grazieService: new GrazieService(
            `${this.llmServicesLogsDir}grazie-logs.txt`,
            this.eventLogger
        ),
        predefinedProofsService: new PredefinedProofsService(
            `${this.llmServicesLogsDir}predefined-proofs-logs.txt`
        ),
        lmStudioService: new LMStudioService(
            `${this.llmServicesLogsDir}lmstudio-logs.txt`,
            this.eventLogger
        ),
    };

    constructor() {}

    private parseLoggingVerbosity(config: WorkspaceConfiguration): Severity {
        const verbosity = config.get("loggingVerbosity");
        switch (verbosity) {
            case "info":
                return Severity.INFO;
            case "debug":
                return Severity.DEBUG;
            default:
                throw new Error(`Unknown logging verbosity: ${verbosity}`);
        }
    }

    dispose(): void {
        this.llmServices.openAiService.dispose();
        this.llmServices.grazieService.dispose();
        this.llmServices.predefinedProofsService.dispose();
        this.llmServices.lmStudioService.dispose();
        this.logWriter.dispose();
        fs.rmSync(this.llmServicesLogsDir, { recursive: true, force: true });
    }
}

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

export class CoqPilot {
    private readonly globalExtensionState: GlobalExtensionState;
    private readonly vscodeExtensionContext: ExtensionContext;

    private readonly jsonSchemaValidator: Ajv;

    constructor(vscodeExtensionContext: ExtensionContext) {
        hideAuxFiles();
        suggestAddingAuxFilesToGitignore();

        this.vscodeExtensionContext = vscodeExtensionContext;
        this.globalExtensionState = new GlobalExtensionState();

        this.registerEditorCommand(
            "perform_completion_under_cursor",
            this.performCompletionUnderCursor.bind(this)
        );
        this.registerEditorCommand(
            "perform_completion_in_selection",
            this.performCompletionInSelection.bind(this)
        );
        this.registerEditorCommand(
            "perform_completion_for_all_admits",
            this.performCompletionForAllAdmits.bind(this)
        );

        this.jsonSchemaValidator = new Ajv();

        this.vscodeExtensionContext.subscriptions.push(this);
    }

    async performCompletionUnderCursor(editor: TextEditor) {
        const cursorPosition = editor.selection.active;
        this.performSpecificCompletionsWithProgress(
            (hole) => positionInRange(cursorPosition, hole.range),
            editor
        );
    }

    async performCompletionInSelection(editor: TextEditor) {
        const selection = editor.selection;
        this.performSpecificCompletionsWithProgress(
            (hole) => selection.contains(toVSCodePosition(hole.range.start)),
            editor
        );
    }

    async performCompletionForAllAdmits(editor: TextEditor) {
        this.performSpecificCompletionsWithProgress((_hole) => true, editor);
    }

    private checkUserProvidedApiKeys(
        processEnvironment: ProcessEnvironment
    ): boolean {
        if (
            processEnvironment.modelsParams.openAiParams.some(
                (params) => params.apiKey === "None"
            )
        ) {
            showApiKeyNotProvidedMessage("openai", pluginId);
            return false;
        } else if (
            processEnvironment.modelsParams.grazieParams.some(
                (params) => params.apiKey === "None"
            )
        ) {
            showApiKeyNotProvidedMessage("grazie", pluginId);
            return false;
        }

        return true;
    }

    private async performSpecificCompletionsWithProgress(
        shouldCompleteHole: (hole: ProofStep) => boolean,
        editor: TextEditor
    ) {
        await window.withProgress(
            {
                location: ProgressLocation.Window,
                title: `${pluginId}: In progress`,
            },
            async () => {
                try {
                    await this.performSpecificCompletions(
                        shouldCompleteHole,
                        editor
                    );
                } catch (error) {
                    if (error instanceof UserSettingsValidationError) {
                        showMessageToUser(error.toString(), "error");
                    } else if (error instanceof Error) {
                        showMessageToUser(error.message, "error");
                        console.error(error);
                    }
                }
            }
        );
    }

    private async performSpecificCompletions(
        shouldCompleteHole: (hole: ProofStep) => boolean,
        editor: TextEditor
    ) {
        const [completionContexts, sourceFileEnvironment, processEnvironment] =
            await this.prepareForCompletions(
                shouldCompleteHole,
                editor.document.version,
                editor.document.uri.fsPath
            );

        if (!this.checkUserProvidedApiKeys(processEnvironment)) {
            return;
        }

        const unsubscribeCallback = this.subscribeToLLMServiceLogicEvents();
        try {
            let completionPromises = completionContexts.map(
                (completionContext) => {
                    return this.performSingleCompletion(
                        completionContext,
                        sourceFileEnvironment,
                        processEnvironment,
                        editor
                    );
                }
            );

            await Promise.all(completionPromises);
        } finally {
            unsubscribeCallback();
        }
    }

    // returns callback to unsubscribe from these events
    private subscribeToLLMServiceLogicEvents(): () => void {
        const llmServiceToUIState: LLMServiceToUIState =
            this.createLLMServiceToUIState();
        const generationFailedSubscriptionId =
            this.subscribeToGenerationFromChatFailedEvent(llmServiceToUIState);
        const generationSucceededSubscriptionId =
            this.subscribeToGenerationFromChatSucceededEvent(
                llmServiceToUIState
            );
        return () => {
            this.globalExtensionState.eventLogger.unsubscribe(
                LLMService.generationFromChatFailedEvent,
                generationFailedSubscriptionId
            );
            this.globalExtensionState.eventLogger.unsubscribe(
                LLMService.generationFromChatSucceededEvent,
                generationSucceededSubscriptionId
            );
        };
    }

    private createLLMServiceToUIState(): LLMServiceToUIState {
        return {
            [this.globalExtensionState.llmServices.openAiService.serviceName]: {
                availabilityState: LLMServiceAvailablityState.AVAILABLE,
                messagesShownState:
                    LLMServiceMessagesShownState.NO_MESSAGES_SHOWN,
            },
            [this.globalExtensionState.llmServices.grazieService.serviceName]: {
                availabilityState: LLMServiceAvailablityState.AVAILABLE,
                messagesShownState:
                    LLMServiceMessagesShownState.NO_MESSAGES_SHOWN,
            },
            [this.globalExtensionState.llmServices.predefinedProofsService
                .serviceName]: {
                availabilityState: LLMServiceAvailablityState.AVAILABLE,
                messagesShownState:
                    LLMServiceMessagesShownState.NO_MESSAGES_SHOWN,
            },
            [this.globalExtensionState.llmServices.lmStudioService.serviceName]:
                {
                    availabilityState: LLMServiceAvailablityState.AVAILABLE,
                    messagesShownState:
                        LLMServiceMessagesShownState.NO_MESSAGES_SHOWN,
                },
        };
    }

    private subscribeToGenerationFromChatFailedEvent(
        llmServiceToUIState: LLMServiceToUIState
    ): SubscriptionId {
        const callback = (data: any) => {
            const [llmService, uiState] =
                CoqPilot.parseLLMServiceLogicEventData(
                    data,
                    llmServiceToUIState
                );
            const serviceName = llmService.serviceName;
            if (
                uiState.availabilityState ===
                LLMServiceAvailablityState.AVAILABLE
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
        return this.globalExtensionState.eventLogger.subscribeToLogicEvent(
            LLMService.generationFromChatFailedEvent,
            callback
        );
    }

    private subscribeToGenerationFromChatSucceededEvent(
        llmServiceToUIState: LLMServiceToUIState
    ): SubscriptionId {
        const callback = (data: any) => {
            const [llmService, uiState] =
                CoqPilot.parseLLMServiceLogicEventData(
                    data,
                    llmServiceToUIState
                );
            const serviceName = llmService.serviceName;
            if (
                uiState.availabilityState ===
                LLMServiceAvailablityState.UNAVAILABLE
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
        return this.globalExtensionState.eventLogger.subscribeToLogicEvent(
            LLMService.generationFromChatSucceededEvent,
            callback
        );
    }

    private static parseLLMServiceLogicEventData(
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

    private async performSingleCompletion(
        completionContext: CompletionContext,
        sourceFileEnvironment: SourceFileEnvironment,
        processEnvironment: ProcessEnvironment,
        editor: TextEditor
    ) {
        const result = await generateCompletion(
            completionContext,
            sourceFileEnvironment,
            processEnvironment,
            this.globalExtensionState.eventLogger
        );

        if (result instanceof SuccessGenerationResult) {
            const flatProof = this.prepareCompletionForInsertion(result.data);
            const vscodeHoleRange = toVSCodeRange({
                start: completionContext.prefixEndPosition,
                end: completionContext.admitEndPosition,
            });
            const completionRange = toVSCodeRange({
                start: completionContext.prefixEndPosition,
                end: {
                    line: completionContext.prefixEndPosition.line,
                    character:
                        completionContext.prefixEndPosition.character +
                        flatProof.length,
                },
            });

            await deleteTextFromRange(editor, vscodeHoleRange);
            await insertCompletion(
                editor,
                flatProof,
                toVSCodePosition(completionContext.prefixEndPosition)
            );
            highlightTextInEditor(completionRange);
        } else if (result instanceof FailureGenerationResult) {
            switch (result.status) {
                case FailureGenerationStatus.excededTimeout:
                    showMessageToUser(EditorMessages.timeoutError, "info");
                    break;
                case FailureGenerationStatus.exception:
                    showMessageToUser(
                        EditorMessages.exceptionError(result.message),
                        "error"
                    );
                    break;
                case FailureGenerationStatus.searchFailed:
                    const completionLine =
                        completionContext.prefixEndPosition.line + 1;
                    showMessageToUser(
                        EditorMessages.noProofsForAdmit(completionLine),
                        "info"
                    );
                    break;
            }
        }
    }

    private prepareCompletionForInsertion(text: string) {
        const flatProof = text.replace(/\n/g, " ");
        return flatProof
            .trim()
            .slice(1, flatProof.length - 2)
            .trim();
    }

    private async prepareForCompletions(
        shouldCompleteHole: (hole: ProofStep) => boolean,
        fileVersion: number,
        filePath: string
    ): Promise<
        [CompletionContext[], SourceFileEnvironment, ProcessEnvironment]
    > {
        const fileUri = Uri.fromPath(filePath);
        const coqLspServerConfig = CoqLspConfig.createServerConfig();
        const coqLspClientConfig = CoqLspConfig.createClientConfig();
        const client = new CoqLspClient(coqLspServerConfig, coqLspClientConfig);
        const contextTheoremsRanker = this.buildTheoremsRankerFromConfig();

        const coqProofChecker = new CoqProofChecker(client);
        const [completionContexts, sourceFileEnvironment] =
            await inspectSourceFile(
                fileVersion,
                shouldCompleteHole,
                fileUri,
                client
            );
        const processEnvironment: ProcessEnvironment = {
            coqProofChecker: coqProofChecker,
            modelsParams: this.parseUserModelsParams(
                workspace.getConfiguration(pluginId)
            ),
            services: this.globalExtensionState.llmServices,
            theoremRanker: contextTheoremsRanker,
        };

        return [completionContexts, sourceFileEnvironment, processEnvironment];
    }

    private buildTheoremsRankerFromConfig(): ContextTheoremsRanker {
        const workspaceConfig = workspace.getConfiguration(pluginId);
        const rankerType = workspaceConfig.contextTheoremsRankerType;

        switch (rankerType) {
            case "distance":
                return new DistanceContextTheoremsRanker();
            case "random":
                return new RandomContextTheoremsRanker();
            default:
                throw new Error(
                    `Unknown context theorems ranker type: ${rankerType}`
                );
        }
    }

    private parseUserModelsParams(
        config: WorkspaceConfiguration
    ): UserModelsParams {
        const openAiParams: OpenAiUserModelParams[] =
            config.openAiModelsParameters.map((params: any) =>
                this.validateAndParseJson(params, openAiUserModelParamsSchema)
            );
        const grazieParams: GrazieUserModelParams[] =
            config.grazieModelsParameters.map((params: any) =>
                this.validateAndParseJson(params, grazieUserModelParamsSchema)
            );
        const predefinedProofsParams: PredefinedProofsUserModelParams[] =
            config.predefinedProofsModelsParameters.map((params: any) =>
                this.validateAndParseJson(
                    params,
                    predefinedProofsUserModelParamsSchema
                )
            );
        const lmStudioParams: LMStudioUserModelParams[] =
            config.lmStudioModelsParameters.map((params: any) =>
                this.validateAndParseJson(params, lmStudioUserModelParamsSchema)
            );

        return {
            openAiParams: openAiParams,
            grazieParams: grazieParams,
            predefinedProofsModelParams: predefinedProofsParams,
            lmStudioParams: lmStudioParams,
        };
    }

    private validateAndParseJson<T>(
        json: any,
        targetClassSchema: JSONSchemaType<T>
    ): T {
        const instance: T = json as T;
        const validate = this.jsonSchemaValidator.compile(targetClassSchema);
        if (!validate(instance)) {
            throw new UserSettingsValidationError(
                `Unable to validate json against the class: ${JSON.stringify(validate.errors)}`,
                targetClassSchema.title ?? "Unknown"
            );
        }

        return instance;
    }

    private registerEditorCommand(
        command: string,
        fn: (editor: TextEditor) => void
    ) {
        let disposable = commands.registerTextEditorCommand(
            `${pluginId}.` + command,
            fn
        );
        this.vscodeExtensionContext.subscriptions.push(disposable);
    }

    dispose(): void {
        cleanAuxFiles();
        this.globalExtensionState.dispose();
    }
}

class UserSettingsValidationError extends Error {
    constructor(
        message: string,
        public readonly settingsName: string
    ) {
        super(message);
    }

    toString(): string {
        return `Unable to validate user settings for ${this.settingsName}. Please refer to the README for the correct settings format: https://github.com/JetBrains-Research/coqpilot/blob/main/README.md#guide-to-model-configuration.`;
    }
}
