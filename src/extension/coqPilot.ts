import {
    ExtensionContext as VSCodeContext,
    TextEditor,
    commands,
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
import { PluginState } from "./globalExtensionState";
import { PluginStatusIndicator } from "./pluginStatusIndicator";
import { subscribeToHandleLLMServicesEvents } from "./llmServicesEventsHandler";
import {
    positionInRange,
    toVSCodePosition,
    toVSCodeRange,
} from "./positionRangeUtils";
import { SessionState } from "./sessionExtensionState";
import { SettingsValidationError } from "./settingsValidationError";

export const pluginId = "coqpilot";
export const pluginName = "CoqPilot";

export class CoqPilot {
    private readonly pluginStatusIndicator: PluginStatusIndicator;

    private constructor(
        private readonly vscodeContext: VSCodeContext,
        private readonly pluginState: PluginState,
        private sessionState: SessionState
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
        this.pluginStatusIndicator = new PluginStatusIndicator(
            `${pluginId}.${toggleCommand}`,
            vscodeContext
        );
        this.pluginStatusIndicator.updateStatusBar(true);

        this.vscodeContext.subscriptions.push(this);
    }

    static async create(vscodeExtensionContext: VSCodeContext) {
        const globalExtensionState = new PluginState();
        const sessionExtensionState = await SessionState.create(
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
            this.sessionState.abortController.signal
        );
    }

    async performCompletionInSelection(editor: TextEditor) {
        const selection = editor.selection;
        this.performSpecificCompletionsWithProgress(
            (hole) => selection.contains(toVSCodePosition(hole.range.start)),
            editor,
            this.sessionState.abortController.signal
        );
    }

    async performCompletionForAllAdmits(editor: TextEditor) {
        this.performSpecificCompletionsWithProgress(
            (_hole) => true,
            editor,
            this.sessionState.abortController.signal
        );
    }

    async toggleCurrentSession() {
        if (this.pluginState.hasActiveSession) {
            this.pluginState.hasActiveSession = false;
            this.sessionState.abort();
            this.sessionState.dispose();
            this.pluginStatusIndicator.updateStatusBar(false);
        } else {
            this.sessionState = await SessionState.create(
                this.pluginState.logOutputChannel,
                this.pluginState.eventLogger
            );
            this.pluginState.hasActiveSession = true;
            this.pluginStatusIndicator.updateStatusBar(true);
        }
    }

    private async performSpecificCompletionsWithProgress(
        shouldCompleteHole: (hole: ProofStep) => boolean,
        editor: TextEditor,
        abortSignal: AbortSignal
    ) {
        if (!this.pluginState.hasActiveSession) {
            showMessageToUser(EditorMessages.extensionIsPaused, "warning");
            return;
        }
        try {
            this.pluginStatusIndicator.showInProgressSpinner();

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
            } else if (
                e instanceof CompletionAbortError ||
                !this.pluginState.hasActiveSession
            ) {
                showMessageToUser(EditorMessages.completionAborted, "info");
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
            this.pluginStatusIndicator.hideInProgressSpinner(
                this.pluginState.hasActiveSession
            );
        }
    }

    private async performSpecificCompletions(
        shouldCompleteHole: (hole: ProofStep) => boolean,
        editor: TextEditor,
        abortSignal: AbortSignal
    ) {
        this.pluginState.eventLogger.log(
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
        this.pluginState.eventLogger.log(
            "completion-preparation-finished",
            `CoqPilot has successfully parsed the file with ${sourceFileEnvironment.fileTheorems.length} theorems and has found ${completionContexts.length} admits inside chosen selection`
        );

        if (completionContexts.length === 0) {
            showMessageToUser(EditorMessages.noAdmitsFound, "warning");
            return;
        }

        const unsubscribeFromLLMServicesEventsCallback =
            subscribeToHandleLLMServicesEvents(
                this.pluginState.llmServices,
                this.pluginState.eventLogger
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
            this.pluginState.eventLogger
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
            this.sessionState.coqLspClient
        );
        const [completionContexts, sourceFileEnvironment] =
            await inspectSourceFile(
                documentVersion,
                shouldCompleteHole,
                fileUri,
                this.sessionState.coqLspClient,
                abortSignal,
                contextTheoremsRanker.needsUnwrappedNotations,
                this.pluginState.eventLogger
            );
        const processEnvironment: ProcessEnvironment = {
            coqProofChecker: coqProofChecker,
            modelsParams: readAndValidateUserModelsParams(
                workspace.getConfiguration(pluginId),
                this.pluginState.llmServices
            ),
            services: this.pluginState.llmServices,
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
        this.vscodeContext.subscriptions.push(disposable);
    }

    dispose(): void {
        this.vscodeContext.subscriptions.forEach((d) => d.dispose());
        this.sessionState.dispose();
        this.pluginState.dispose();
    }
}
