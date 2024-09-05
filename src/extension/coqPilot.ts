import {
    ExtensionContext,
    ProgressLocation,
    TextEditor,
    commands,
    window,
    workspace,
} from "vscode";

import { CoqLspClient } from "../coqLsp/coqLspClient";
import { CoqLspConfig } from "../coqLsp/coqLspConfig";
import { CoqLspStartupError } from "../coqLsp/coqLspTypes";

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
import { CoqProofChecker } from "../core/coqProofChecker";
import { inspectSourceFile } from "../core/inspectSourceFile";

import { ProofStep } from "../coqParser/parsedTypes";
import { Uri } from "../utils/uri";

import {
    buildTheoremsRankerFromConfig,
    parseCoqLspServerPath,
    readAndValidateUserModelsParams,
} from "./configReaders";
import {
    deleteTextFromRange,
    highlightTextInEditor,
    insertCompletion,
} from "./documentEditor";
import { suggestAddingAuxFilesToGitignore } from "./editGitignoreCommand";
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
import { cleanAuxFiles, hideAuxFiles } from "./tmpFilesCleanup";

export const pluginId = "coqpilot";
export const pluginName = "CoqPilot";

export class CoqPilot {
    private readonly globalExtensionState: GlobalExtensionState;
    private readonly vscodeExtensionContext: ExtensionContext;

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

    private async performSpecificCompletionsWithProgress(
        shouldCompleteHole: (hole: ProofStep) => boolean,
        editor: TextEditor
    ) {
        await window.withProgress(
            {
                location: ProgressLocation.Window,
                title: `${pluginName}: In progress`,
            },
            async () => {
                try {
                    await this.performSpecificCompletions(
                        shouldCompleteHole,
                        editor
                    );
                } catch (error) {
                    if (error instanceof SettingsValidationError) {
                        error.showAsMessageToUser();
                    } else if (error instanceof CoqLspStartupError) {
                        showMessageToUserWithSettingsHint(
                            EditorMessages.coqLspStartupFailure(error.path),
                            "error",
                            `${pluginId}.coqLspServerPath`
                        );
                    } else if (error instanceof Error) {
                        showMessageToUser(
                            EditorMessages.errorOccurred(error.message),
                            "error"
                        );
                        console.error(`${error.stack ?? error}`);
                    }
                }
            }
        );
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
        const coqLspServerPath = parseCoqLspServerPath();
        const coqLspClientConfig =
            CoqLspConfig.createClientConfig(coqLspServerPath);
        const client = await CoqLspClient.create(
            coqLspServerConfig,
            coqLspClientConfig
        );
        const contextTheoremsRanker = buildTheoremsRankerFromConfig();

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
        cleanAuxFiles();
        this.globalExtensionState.dispose();
    }
}
