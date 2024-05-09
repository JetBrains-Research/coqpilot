import Ajv from "ajv";
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
    parseAndValidateUserModelsParams,
} from "./configParser";
import {
    deleteTextFromRange,
    highlightTextInEditor,
    insertCompletion,
} from "./documentEditor";
import {
    EditorMessages,
    showMessageToUser,
    suggestAddingAuxFilesToGitignore,
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
                    if (error instanceof SettingsValidationError) {
                        error.showAsMessageToUser();
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
                case FailureGenerationStatus.timeoutExceeded:
                    showMessageToUser(EditorMessages.timeoutExceeded, "info");
                    break;
                case FailureGenerationStatus.errorOccurred:
                    showMessageToUser(
                        EditorMessages.errorOccurred(result.message),
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
            modelsParams: parseAndValidateUserModelsParams(
                workspace.getConfiguration(pluginId),
                this.jsonSchemaValidator
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
