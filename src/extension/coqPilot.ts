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
import { logExecutionTime } from "../logging/timeMeasureDecorator";
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
import { GlobalExtensionState } from "./globalExtensionState";
import { subscribeToHandleLLMServicesEvents } from "./llmServicesEventsHandler";
import {
    positionInRange,
    toVSCodePosition,
    toVSCodeRange,
} from "./positionRangeUtils";
import { SettingsValidationError } from "./settingsValidationError";
import { StatusBarButton } from "./statusBarButton";

export const pluginId = "coqpilot";
export const pluginName = "CoqPilot";

export class CoqPilot {
    private readonly globalExtensionState: GlobalExtensionState;
    private readonly vscodeExtensionContext: ExtensionContext;
    private subscriptions: { dispose(): any }[] = [];

    private constructor(
        vscodeExtensionContext: ExtensionContext,
        globalExtensionState: GlobalExtensionState,
        private readonly statusBarButton: StatusBarButton
    ) {
        this.vscodeExtensionContext = vscodeExtensionContext;
        this.globalExtensionState = globalExtensionState;

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

        this.vscodeExtensionContext.subscriptions.push(this);
    }

    static async create(
        vscodeExtensionContext: ExtensionContext,
        statusBarItem: StatusBarButton
    ) {
        const globalExtensionState = await GlobalExtensionState.create();
        return new CoqPilot(
            vscodeExtensionContext,
            globalExtensionState,
            statusBarItem
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
        try {
            this.statusBarButton.showSpinner();

            await this.performSpecificCompletions(shouldCompleteHole, editor);
        } catch (e) {
            if (e instanceof SettingsValidationError) {
                e.showAsMessageToUser();
            } else if (e instanceof CoqLspStartupError) {
                showMessageToUserWithSettingsHint(
                    EditorMessages.coqLspStartupFailure(e.path),
                    "error",
                    `${pluginId}.coqLspServerPath`
                );
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
            this.statusBarButton.hideSpinner();
        }
    }

    private async performSpecificCompletions(
        shouldCompleteHole: (hole: ProofStep) => boolean,
        editor: TextEditor
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
                editor.document.uri.fsPath
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
                        editor
                    );
                }
            );

            await Promise.all(completionPromises);
        } finally {
            unsubscribeFromLLMServicesEventsCallback();
        }
    }

    @logExecutionTime
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

    @logExecutionTime
    private async prepareForCompletions(
        shouldCompleteHole: (hole: ProofStep) => boolean,
        documentVersion: number,
        filePath: string
    ): Promise<
        [CompletionContext[], SourceFileEnvironment, ProcessEnvironment]
    > {
        const fileUri = Uri.fromPath(filePath);
        const contextTheoremsRanker = buildTheoremsRankerFromConfig();

        const coqProofChecker = new CoqProofChecker(
            this.globalExtensionState.coqLspClient
        );
        const [completionContexts, sourceFileEnvironment] =
            await inspectSourceFile(
                documentVersion,
                shouldCompleteHole,
                fileUri,
                this.globalExtensionState.coqLspClient,
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
        this.subscriptions.push(disposable);
    }

    dispose(): void {
        // This is not the same as vscodeExtensionContext.subscriptions
        // As it doesn't contain the statusBar item and the toggle command
        this.subscriptions.forEach((d) => d.dispose());
        this.globalExtensionState.dispose();
    }
}
