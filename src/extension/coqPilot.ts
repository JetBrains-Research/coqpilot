import { OpenAiService } from "../llm/llmService/openai/openAiService";
import { GrazieService } from "../llm/llmService/grazie/grazieService";
import { 
    PredefinedProofsService 
} from "../llm/llmService/predefinedProofs/predefinedProofsService";
import { CoqLspConfig } from "../coqLsp/coqLspConfig";
import { CoqLspClient } from "../coqLsp/coqLspClient";
import { inspectSourceFile } from "../core/inspectSourceFile";
import { CoqProofChecker } from "../core/coqProofChecker";
import { Uri } from "../utils/uri";
import { 
    positionInRange,
    toVSCodePosition, 
    toVSCodeRange
} from "../utils/editor";
import { generateCompletion } from "../core/completionGenerator";
import * as messages from "./documentEditor";

import { 
    SuccessGenerationResult, 
    FailureGenerationResult
} from "../core/completionGenerator";

import { 
    ProcessEnvironment,
    SourceFileEnvironment,
    CompletionContext
} from "../core/completionGenerator";

import { 
    ModelsParams,
    LLMServices
} from "../llm/configurations";

import {
    commands,
    ExtensionContext,
    workspace,
    TextEditor,
} from "vscode";
import { ProofStep } from "../coqParser/parsedTypes";

export class GlobalExtensionState {
    constructor(
        public readonly llmServices: LLMServices,
    ) {}

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

    constructor(vscodeExtensionContext: ExtensionContext) {
        this.excludeAuxFiles();
        this.vscodeExtensionContext = vscodeExtensionContext;
        this.globalExtensionState = new GlobalExtensionState({
            openAiService: new OpenAiService(),
            grazieService: new GrazieService(),
            predefinedProofsService: new PredefinedProofsService()
        });

        this.registerEditorCommand("perform_completion_under_cursor", this.performCompletionUnderCursor.bind(this));
        this.registerEditorCommand("perform_completion_in_selection", this.performCompletionInSelection.bind(this));
        this.registerEditorCommand("perform_completion_for_all_admits", this.performCompletionForAllAdmits.bind(this));

        this.vscodeExtensionContext.subscriptions.push(this);
    }

    async performCompletionUnderCursor(
        editor: TextEditor
    ) {
        const cursorPosition = editor.selection.active;
        this.performSpecificCompletions(
            (hole) => positionInRange(cursorPosition, hole.range),
            editor
        );
    }

    async performCompletionInSelection(
        editor: TextEditor
    ) {
        const selection = editor.selection;
        this.performSpecificCompletions(
            (hole) => selection.contains(toVSCodePosition(hole.range.start)),
            editor
        );
    }

    async performCompletionForAllAdmits(
        editor: TextEditor
    ) {
        this.performSpecificCompletions(
            (_hole) => true,
            editor
        );
    }

    private async performSpecificCompletions(
        shouldCompleteHole: (hole: ProofStep) => boolean,
        editor: TextEditor
    ) {
        const [completionContexts, sourceFileEnvironment, processEnvironment] = await this.prepareForCompletions(
            shouldCompleteHole,
            editor.document.version,
            editor.document.uri.fsPath
        );

        for (const completionContext of completionContexts) {
            await this.performSingleCompletion(
                completionContext,
                sourceFileEnvironment,
                processEnvironment,
                editor
            );
        }
    }

    private async performSingleCompletion(
        completionContext: CompletionContext,
        sourceFileEnvironment: SourceFileEnvironment,
        processEnvironment: ProcessEnvironment,
        editor: TextEditor,
    ) {
        const result = await generateCompletion(
            completionContext,
            sourceFileEnvironment,
            processEnvironment
        );

        if (result instanceof SuccessGenerationResult) {
            const proofWithIndent = this.prepareCompletionForInsertion(result.data);
            await messages.deleteTextFromRange(
                editor, toVSCodeRange({
                    start: completionContext.prefixEndPosition,
                    end: completionContext.admitEndPosition
                })
            );

            await messages.insertCompletion(
                editor, proofWithIndent, toVSCodePosition(completionContext.prefixEndPosition)
            );
        } else if (result instanceof FailureGenerationResult) {
            const status = (function() {
                switch (result.status) {
                    case 0: return "timeout";
                    case 1: return "exception";
                    case 2: return "searchFailed";
                    default: return "unknown";
                }
            })();

            console.log("Failed with: ", result.message, status);
        }
    }

    private prepareCompletionForInsertion(text: string) {
        const flatProof = text.replace(/\n/g, ' ');
        return flatProof.trim().slice(1, flatProof.length - 2).trim();
    }

    private async prepareForCompletions(
        shouldCompleteHole: (hole: ProofStep) => boolean,
        fileVersion: number, 
        filePath: string,
    ): Promise<[CompletionContext[], SourceFileEnvironment, ProcessEnvironment]> {
        const fileUri = Uri.fromPath(filePath);
        const coqLspServerConfig = CoqLspConfig.createServerConfig();
        const coqLspClientConfig = CoqLspConfig.createClientConfig();        
        const client = new CoqLspClient(coqLspServerConfig, coqLspClientConfig);

        const coqProofChecker = new CoqProofChecker(client);
        const [completionContexts, sourceFileEnvironment] = await inspectSourceFile(
            fileVersion,
            shouldCompleteHole,
            fileUri,
            client
        );
        const processEnvironment: ProcessEnvironment = {
            coqProofChecker: coqProofChecker,
            modelsParams: this.buildModelsParamsFromConfig(),
            services: this.globalExtensionState.llmServices
        };

        return [completionContexts, sourceFileEnvironment, processEnvironment];
    }

    private buildModelsParamsFromConfig(): ModelsParams {
        const workspaceConfig = workspace.getConfiguration(this.pluginId);
        try {
            return {
                openAiParams: [
                    {
                        prompt: `Generate proof of the theorem from user input in Coq. You should only generate proofs in Coq. Never add special comments to the proof. Your answer should be a valid Coq proof. It should start with 'Proof.' and end with 'Qed.'.`,
                        maxTokens: workspaceConfig.maxNumberOfTokens,
                        temperature: 1.0,
                        model: workspaceConfig.gptModel,
                        apiKey: workspaceConfig.openAiApiKey,
                        choices: workspaceConfig.proofAttemptsPerOneTheorem
                    }
                ],
                grazieParams: [],
                predefinedProofsModelParams: [
                    {
                        tactics: workspaceConfig.extraCommandsList
                    }
                ]
            };
        } catch (error: any) {
            console.error(error);
            throw new Error(`Failed to build models params with Error: ${error.message}`);
        }
    }

    private registerEditorCommand(command: string, fn: (editor: TextEditor) => void) {
        let disposable = commands.registerTextEditorCommand(
            "coqpilot." + command,
            fn
        );
        this.vscodeExtensionContext.subscriptions.push(disposable);
    }

    excludeAuxFiles() {
        // Hide files generated to check proofs
        let activationConfig = workspace.getConfiguration();
        let fexc: any = activationConfig.get("files.exclude");
        activationConfig.update("files.exclude", {
            ...fexc,
            // eslint-disable-next-line @typescript-eslint/naming-convention
            '**/*_cp_aux.v': true,
        });
    }

    dispose(): void {
        this.globalExtensionState.dispose();
    }

}