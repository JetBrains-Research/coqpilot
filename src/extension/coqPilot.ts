import {
    ExtensionContext, // ProgressLocation,
    TextEditor,
    commands, // window,
    workspace,
} from "vscode";

import { CoqLspStartupError } from "../coqLsp/coqLspTypes";

import {
    CompletionContext,
    ProcessEnvironment,
    SourceFileEnvironment,
} from "../core/completionGenerationContext";
import { generateCompletion } from "../core/completionGenerator";
import {
    FailureGenerationResult,
    FailureGenerationStatus,
    SuccessGenerationResult,
} from "../core/completionGenerator";
import { CoqProofChecker } from "../core/coqProofChecker";
import { inspectSourceFile } from "../core/inspectSourceFile";

import { ProofStep } from "../coqParser/parsedTypes";
import { buildErrorCompleteLog } from "../utils/errorsUtils";
import { sleep } from "../utils/sleep";
import { Uri } from "../utils/uri";

import {
    buildTheoremsRankerFromConfig,
    readAndValidateUserModelsParams,
} from "./configReaders";
import {
    deleteTextFromRange,
    highlightTextInEditor,
    insertCompletion,
} from "./documentEditor";
import {
    EditorMessages,
    showMessageToUser,
    showMessageToUserWithSettingsHint,
} from "./editorMessages";
import { CompletionAbortError, throwOnAbort } from "./extensionAbortUtils";
import { GlobalExtensionState } from "./globalExtensionState";
import { HealthStatusIndicator } from "./healthStatusIndicator";
import { subscribeToHandleLLMServicesEvents } from "./llmServicesEventsHandler";
import {
    positionInRange,
    toVSCodePosition,
    toVSCodeRange,
} from "./positionRangeUtils";
import { SessionExtensionState } from "./sessionExtensionState";
import { SettingsValidationError } from "./settingsValidationError";

export const pluginId = "coqpilot";
export const pluginName = "CoqPilot";

export class CoqPilot {
    private readonly healthStatusIndicator: HealthStatusIndicator;

    private constructor(
        private readonly vscodeExtensionContext: ExtensionContext,
        private readonly globalExtensionState: GlobalExtensionState,
        private sessionExtensionState: SessionExtensionState
    ) {
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

        const toggleCommand = `toggle_current_session`;
        this.registerEditorCommand(
            toggleCommand,
            this.toggleCurrentSession.bind(this)
        );
        this.healthStatusIndicator = new HealthStatusIndicator(
            `${pluginId}.${toggleCommand}`,
            vscodeExtensionContext
        );
        this.healthStatusIndicator.updateStatusBar(true);

        this.vscodeExtensionContext.subscriptions.push(this);
    }

    static async create(vscodeExtensionContext: ExtensionContext) {
        const globalExtensionState = new GlobalExtensionState();
        const sessionExtensionState = await SessionExtensionState.create(
            globalExtensionState.logOutputChannel,
            globalExtensionState.eventLogger
        );
        return new CoqPilot(
            vscodeExtensionContext,
            globalExtensionState,
            sessionExtensionState
        );
    }

    async performCompletionUnderCursor(editor: TextEditor) {
        const cursorPosition = editor.selection.active;
        this.performSpecificCompletionsWithProgress(
            (hole) => positionInRange(cursorPosition, hole.range),
            editor,
            this.sessionExtensionState.abortController.signal
        );
    }

    async performCompletionInSelection(editor: TextEditor) {
        const selection = editor.selection;
        this.performSpecificCompletionsWithProgress(
            (hole) => selection.contains(toVSCodePosition(hole.range.start)),
            editor,
            this.sessionExtensionState.abortController.signal
        );
    }

    async performCompletionForAllAdmits(editor: TextEditor) {
        this.performSpecificCompletionsWithProgress(
            (_hole) => true,
            editor,
            this.sessionExtensionState.abortController.signal
        );
    }

    async toggleCurrentSession() {
        if (this.globalExtensionState.hasActiveSession) {
            this.sessionExtensionState.abort();
            // TODO: [LspCoreRefactor] Change this. Need to reach the throwOnAbort 
            // checkpoint before disposing the LSP client.
            await sleep(500);
            this.sessionExtensionState.dispose();
            this.globalExtensionState.hasActiveSession = false;
            this.healthStatusIndicator.updateStatusBar(false);
        } else {
            this.sessionExtensionState = await SessionExtensionState.create(
                this.globalExtensionState.logOutputChannel,
                this.globalExtensionState.eventLogger
            );
            this.globalExtensionState.hasActiveSession = true;
            this.healthStatusIndicator.updateStatusBar(true);
        }
    }

    private async performSpecificCompletionsWithProgress(
        shouldCompleteHole: (hole: ProofStep) => boolean,
        editor: TextEditor,
        abortSignal: AbortSignal
    ) {
        if (!this.globalExtensionState.hasActiveSession) {
            showMessageToUser(EditorMessages.extensionIsPaused, "warning");
            return;
        }
        let isSessionHealthy = true;
        try {
            this.healthStatusIndicator.showSpinner();

            await this.performSpecificCompletions(
                shouldCompleteHole,
                editor,
                abortSignal
            );
        } catch (e) {
            if (e instanceof SettingsValidationError) {
                e.showAsMessageToUser();
            } else if (e instanceof CoqLspStartupError) {
                showMessageToUserWithSettingsHint(
                    EditorMessages.coqLspStartupFailure(e.path),
                    "error",
                    `${pluginId}.coqLspServerPath`
                );
            } else if (e instanceof CompletionAbortError) {
                showMessageToUser(EditorMessages.completionAborted, "info");
                isSessionHealthy = false;
            } else {
                showMessageToUser(
                    e instanceof Error
                        ? EditorMessages.errorOccurred(e.message)
                        : EditorMessages.objectWasThrownAsError(e),
                    "error"
                );
                console.error(buildErrorCompleteLog(e));
            }
        } finally {
            this.healthStatusIndicator.hideSpinner(isSessionHealthy);
        }
    }

    private async performSpecificCompletions(
        shouldCompleteHole: (hole: ProofStep) => boolean,
        editor: TextEditor,
        abortSignal: AbortSignal
    ) {
        this.globalExtensionState.eventLogger.log(
            "completion-started",
            "CoqPilot has started the completion process"
        );

        if (editor.document.isDirty) {
            showMessageToUser(
                EditorMessages.saveFileBeforeCompletion,
                "warning"
            );
            return;
        }

        const [completionContexts, sourceFileEnvironment, processEnvironment] =
            await this.prepareForCompletions(
                shouldCompleteHole,
                editor.document.version,
                editor.document.uri.fsPath,
                abortSignal
            );
        this.globalExtensionState.eventLogger.log(
            "completion-preparation-finished",
            `CoqPilot has successfully parsed the file with ${sourceFileEnvironment.fileTheorems.length} theorems and has found ${completionContexts.length} admits inside chosen selection`
        );

        if (completionContexts.length === 0) {
            showMessageToUser(EditorMessages.noAdmitsFound, "warning");
            return;
        }

        const unsubscribeFromLLMServicesEventsCallback =
            subscribeToHandleLLMServicesEvents(
                this.globalExtensionState.llmServices,
                this.globalExtensionState.eventLogger
            );

        try {
            let completionPromises = completionContexts.map(
                (completionContext) => {
                    return this.performSingleCompletion(
                        completionContext,
                        sourceFileEnvironment,
                        processEnvironment,
                        editor,
                        abortSignal
                    );
                }
            );

            await Promise.all(completionPromises);
        } finally {
            unsubscribeFromLLMServicesEventsCallback();
        }
    }

    private async performSingleCompletion(
        completionContext: CompletionContext,
        sourceFileEnvironment: SourceFileEnvironment,
        processEnvironment: ProcessEnvironment,
        editor: TextEditor,
        abortSignal: AbortSignal
    ) {
        throwOnAbort(abortSignal);
        const result = await generateCompletion(
            completionContext,
            sourceFileEnvironment,
            processEnvironment,
            abortSignal,
            this.globalExtensionState.eventLogger
        );

        if (result instanceof SuccessGenerationResult) {
            const flatProof = this.prepareCompletionForInsertion(result.data);
            const vscodeHoleRange = toVSCodeRange(completionContext.admitRange);
            const completionRange = toVSCodeRange({
                start: completionContext.admitRange.start,
                end: {
                    line: completionContext.admitRange.start.line,
                    character:
                        completionContext.admitRange.start.character +
                        flatProof.length,
                },
            });

            await deleteTextFromRange(editor, vscodeHoleRange);
            await insertCompletion(
                editor,
                flatProof,
                toVSCodePosition(completionContext.admitRange.start)
            );
            highlightTextInEditor(completionRange);
        } else if (result instanceof FailureGenerationResult) {
            switch (result.status) {
                case FailureGenerationStatus.TIMEOUT_EXCEEDED:
                    showMessageToUser(EditorMessages.timeoutExceeded, "info");
                    break;
                case FailureGenerationStatus.ERROR_OCCURRED:
                    showMessageToUser(
                        EditorMessages.errorOccurred(result.message),
                        "error"
                    );
                    break;
                case FailureGenerationStatus.SEARCH_FAILED:
                    const completionLine =
                        completionContext.admitRange.start.line + 1;
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
        documentVersion: number,
        filePath: string,
        abortSignal: AbortSignal
    ): Promise<
        [CompletionContext[], SourceFileEnvironment, ProcessEnvironment]
    > {
        const fileUri = Uri.fromPath(filePath);
        const contextTheoremsRanker = buildTheoremsRankerFromConfig();

        const coqProofChecker = new CoqProofChecker(
            this.sessionExtensionState.coqLspClient
        );
        const [completionContexts, sourceFileEnvironment] =
            await inspectSourceFile(
                documentVersion,
                shouldCompleteHole,
                fileUri,
                this.sessionExtensionState.coqLspClient,
                abortSignal,
                contextTheoremsRanker.needsUnwrappedNotations
            );
        const processEnvironment: ProcessEnvironment = {
            coqProofChecker: coqProofChecker,
            modelsParams: readAndValidateUserModelsParams(
                workspace.getConfiguration(pluginId),
                this.globalExtensionState.llmServices
            ),
            services: this.globalExtensionState.llmServices,
            theoremRanker: contextTheoremsRanker,
        };

        return [completionContexts, sourceFileEnvironment, processEnvironment];
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
        this.vscodeExtensionContext.subscriptions.forEach((d) => d.dispose());
        this.globalExtensionState.dispose();
        this.sessionExtensionState.dispose();
    }
}
