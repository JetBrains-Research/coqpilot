import { OpenAiService } from "../llm/llmServices/openai/openAiService";
import { GrazieService } from "../llm/llmServices/grazie/grazieService";
import { PredefinedProofsService } from "../llm/llmServices/predefinedProofs/predefinedProofsService";
import { CoqLspConfig } from "../coqLsp/coqLspConfig";
import { CoqLspClient } from "../coqLsp/coqLspClient";
import { inspectSourceFile } from "../core/inspectSourceFile";
import { CoqProofChecker } from "../core/coqProofChecker";
import { Uri } from "../utils/uri";

import { hideAuxFiles, cleanAuxFiles } from "./tmpFilesCleanup";
import OutputChannelLogger from "./outputChannelLogger";
import { EventLogger } from "../logging/eventLogger";

import {
    positionInRange,
    toVSCodePosition,
    toVSCodeRange,
} from "./positionRangeUtils";

import { generateCompletion } from "../core/completionGenerator";
import {
    deleteTextFromRange,
    insertCompletion,
    highlightTextInEditor,
} from "./documentEditor";
import Ajv, { JSONSchemaType } from "ajv";

import {
    SuccessGenerationResult,
    FailureGenerationResult,
    FailureGenerationStatus,
} from "../core/completionGenerator";

import {
    ProcessEnvironment,
    SourceFileEnvironment,
    CompletionContext,
} from "../core/completionGenerator";

import { ModelsParams, LLMServices } from "../llm/configurations";

import {
    commands,
    ExtensionContext,
    workspace,
    TextEditor,
    ProgressLocation,
    window,
} from "vscode";
import { ProofStep } from "../coqParser/parsedTypes";
import {
    GrazieModelParams,
    OpenAiModelParams,
    PredefinedProofsModelParams,
    openAiModelParamsSchema,
    grazieModelParamsSchema,
    predefinedProofsModelParamsSchema,
} from "../llm/llmServices/modelParamsInterfaces";

import {
    suggestAddingAuxFilesToGitignore,
    EditorMessages,
    showMessageToUser,
    showApiKeyNotProvidedMessage,
} from "./editorMessages";

import { ContextTheoremsRanker } from "../core/contextTheoremRanker/contextTheoremsRanker";
import { DistanceContextTheoremsRanker } from "../core/contextTheoremRanker/distanceContextTheoremsRanker";
import { RandomContextTheoremsRanker } from "../core/contextTheoremRanker/randomContextTheoremsRanker";

export class GlobalExtensionState {
    constructor(public readonly llmServices: LLMServices) {}

    dispose(): void {
        this.llmServices.openAiService.dispose();
        this.llmServices.grazieService.dispose();
        this.llmServices.predefinedProofsService.dispose();
    }
}

export class CoqPilot {
    private readonly globalExtensionState: GlobalExtensionState;
    private readonly vscodeExtensionContext: ExtensionContext;
    private readonly pluginId = "coqpilot";
    private readonly eventLogger = new EventLogger();

    private readonly jsonSchemaValidator: Ajv;

    constructor(vscodeExtensionContext: ExtensionContext) {
        hideAuxFiles();
        suggestAddingAuxFilesToGitignore();

        this.vscodeExtensionContext = vscodeExtensionContext;
        this.globalExtensionState = new GlobalExtensionState({
            openAiService: new OpenAiService(this.eventLogger),
            grazieService: new GrazieService(this.eventLogger),
            predefinedProofsService: new PredefinedProofsService(),
        });

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
        new OutputChannelLogger(this.eventLogger);

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
            showApiKeyNotProvidedMessage("openai", this.pluginId);
            return false;
        } else if (
            processEnvironment.modelsParams.grazieParams.some(
                (params) => params.apiKey === "None"
            )
        ) {
            showApiKeyNotProvidedMessage("grazie", this.pluginId);
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
                title: `${this.pluginId}: In progress`,
            },
            async () => {
                await this.performSpecificCompletions(
                    shouldCompleteHole,
                    editor
                );
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

        let completionPromises = completionContexts.map((completionContext) => {
            return this.performSingleCompletion(
                completionContext,
                sourceFileEnvironment,
                processEnvironment,
                editor
            );
        });

        await Promise.all(completionPromises);
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
            this.eventLogger
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
            modelsParams: this.buildModelsParamsFromConfig(),
            services: this.globalExtensionState.llmServices,
            theoremRanker: contextTheoremsRanker,
        };

        return [completionContexts, sourceFileEnvironment, processEnvironment];
    }

    private validateAndParseJson<T>(
        json: any,
        targetClassSchema: JSONSchemaType<T>
    ): T {
        const instance: T = json as T;
        const validate = this.jsonSchemaValidator.compile(targetClassSchema);
        if (!validate(instance)) {
            throw new Error(
                `Unable to validate json against the class: ${JSON.stringify(validate.errors)}`
            );
        }

        return instance;
    }

    private buildTheoremsRankerFromConfig(): ContextTheoremsRanker {
        const workspaceConfig = workspace.getConfiguration(this.pluginId);
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

    private buildModelsParamsFromConfig(): ModelsParams {
        const workspaceConfig = workspace.getConfiguration(this.pluginId);

        const openAiParams: OpenAiModelParams[] =
            workspaceConfig.openAiModelsParameters.map((params: any) =>
                this.validateAndParseJson(params, openAiModelParamsSchema)
            );
        const grazieParams: GrazieModelParams[] =
            workspaceConfig.grazieModelsParameters.map((params: any) =>
                this.validateAndParseJson(params, grazieModelParamsSchema)
            );
        const predefinedProofsParams: PredefinedProofsModelParams[] =
            workspaceConfig.predefinedProofsModelsParameters.map(
                (params: any) =>
                    this.validateAndParseJson(
                        params,
                        predefinedProofsModelParamsSchema
                    )
            );

        return {
            openAiParams: openAiParams,
            grazieParams: grazieParams,
            predefinedProofsModelParams: predefinedProofsParams,
        };
    }

    private registerEditorCommand(
        command: string,
        fn: (editor: TextEditor) => void
    ) {
        let disposable = commands.registerTextEditorCommand(
            `${this.pluginId}.` + command,
            fn
        );
        this.vscodeExtensionContext.subscriptions.push(disposable);
    }

    dispose(): void {
        cleanAuxFiles();
        this.globalExtensionState.dispose();
    }
}
