import {
    TextEditor,
    ExtensionContext as VSCodeContext,
    commands,
    workspace,
} from "vscode";

import { CoqLspStartupError } from "../coqLsp/coqLspTypes";

import { CompletionAbortError } from "../core/abortUtils";
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

import { PluginContext } from "./pluginContext";
import { SessionState } from "./sessionState";
import {
    buildTheoremsRankerFromConfig,
    readAndValidateUserModelsParams,
} from "./settings/configReaders";
import { SettingsValidationError } from "./settings/settingsValidationError";
import {
    deleteTextFromRange,
    highlightTextInEditor,
    insertCompletion,
} from "./ui/documentEditor";
import {
    EditorMessages,
    showMessageToUser,
    showMessageToUserWithSettingsHint,
} from "./ui/messages/editorMessages";
import { subscribeToHandleLLMServicesEvents } from "./ui/messages/llmServicesEventsHandler";
import { PluginStatusIndicator } from "./ui/pluginStatusIndicator";
import { pluginId } from "./utils/pluginId";
import {
    positionInRange,
    toVSCodePosition,
    toVSCodeRange,
} from "./utils/positionRangeUtils";

export class CoqPilot {
    private constructor(
        private readonly vscodeContext: VSCodeContext,
        private readonly pluginContext: PluginContext,
        private readonly sessionState: SessionState,
        toggleCommand: string
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

        this.registerCommand(
            toggleCommand,
            this.sessionState.toggleCurrentSession.bind(this.sessionState)
        );

        this.vscodeContext.subscriptions.push(this);
    }

    static async create(vscodeContext: VSCodeContext) {
        const globalExtensionState = new PluginContext();

        const toggleCommand = `toggle_current_session`;
        const pluginStatusIndicator = new PluginStatusIndicator(
            `${pluginId}.${toggleCommand}`,
            vscodeContext
        );

        const sessionExtensionState = await SessionState.create(
            globalExtensionState.logOutputChannel,
            globalExtensionState.eventLogger,
            pluginStatusIndicator
        );

        return new CoqPilot(
            vscodeContext,
            globalExtensionState,
            sessionExtensionState,
            toggleCommand
        );
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

    private async performSpecificCompletionsWithProgress(
        shouldCompleteHole: (hole: ProofStep) => boolean,
        editor: TextEditor
    ) {
        if (!this.sessionState.isActive) {
            showMessageToUser(EditorMessages.extensionIsPaused, "warning");
            return;
        }
        try {
            this.sessionState.showInProgressSpinner();

            await this.performSpecificCompletions(
                shouldCompleteHole,
                editor,
                this.sessionState.abortController.signal
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
                if (!this.sessionState.userNotifiedAboutAbort) {
                    // TODO: potential race condition causeing notification shown twice
                    this.sessionState.markAbortNotificationAsShown();
                    showMessageToUser(EditorMessages.completionAborted, "info");
                }
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
            this.sessionState.hideInProgressSpinner();
        }
    }

    private async performSpecificCompletions(
        shouldCompleteHole: (hole: ProofStep) => boolean,
        editor: TextEditor,
        abortSignal: AbortSignal
    ) {
        this.pluginContext.eventLogger.log(
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
        this.pluginContext.eventLogger.log(
            "completion-preparation-finished",
            `CoqPilot has successfully parsed the file with ${sourceFileEnvironment.fileTheorems.length} theorems and has found ${completionContexts.length} admits inside chosen selection`
        );

        if (completionContexts.length === 0) {
            showMessageToUser(EditorMessages.noAdmitsFound, "warning");
            return;
        }

        const unsubscribeFromLLMServicesEventsCallback =
            subscribeToHandleLLMServicesEvents(
                this.pluginContext.llmServices,
                this.pluginContext.eventLogger
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
        const result = await generateCompletion(
            completionContext,
            sourceFileEnvironment,
            processEnvironment,
            abortSignal,
            this.pluginContext.eventLogger
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
            this.sessionState.coqLspClient,
            this.pluginContext.eventLogger
        );
        // Note: here and later the target file is expected to be opened by the user,
        // so no explicit `coqLspClient.openTextDocument(...)` call is needed
        const [completionContexts, sourceFileEnvironment] =
            await inspectSourceFile(
                documentVersion,
                shouldCompleteHole,
                fileUri,
                this.sessionState.coqLspClient,
                abortSignal,
                contextTheoremsRanker.needsUnwrappedNotations,
                this.pluginContext.eventLogger
            );
        const processEnvironment: ProcessEnvironment = {
            coqProofChecker: coqProofChecker,
            modelsParams: readAndValidateUserModelsParams(
                workspace.getConfiguration(pluginId),
                this.pluginContext.llmServices
            ),
            services: this.pluginContext.llmServices,
            theoremRanker: contextTheoremsRanker,
        };

        return [completionContexts, sourceFileEnvironment, processEnvironment];
    }

    private registerCommand(command: string, fn: () => void) {
        let disposable = commands.registerCommand(`${pluginId}.` + command, fn);
        this.vscodeContext.subscriptions.push(disposable);
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
        this.pluginContext.dispose();
    }
}
