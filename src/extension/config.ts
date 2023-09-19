import * as vscode from 'vscode';
import * as path from 'path';
import { GPT35 } from '../coqLlmInteraction/gpt35';
import { MockLlmPrompt } from '../test/mock/mockllm';
import { LLMInterface } from '../coqLlmInteraction/llmInterface';

export interface CoqpilotConfig {
    coqFilePath: string;
    coqFileRootDir: string;
    openaiApiKey: string;
    proofAttemsPerOneTheorem: number;
    maxNumberOfTokens: number;
    logAttempts: boolean;
    logFolderPath: string | null;
    proofHolesCreateAux: boolean;
    gptModel: string;
    proveAllOnStartup: boolean;
}

export namespace CoqpilotConfig {
    export function create(
        wsConfig: any, 
        editor: vscode.TextEditor, 
        workspaceFolders: readonly vscode.WorkspaceFolder[] | undefined
    ): CoqpilotConfig | undefined {
        try {
            let coqFileRootDir = path.dirname(editor.document.uri.path);
            if (workspaceFolders && workspaceFolders.length > 0) {
                coqFileRootDir = workspaceFolders[0].uri.path;
            }
            return {
                coqFilePath: editor.document.uri.path,
                coqFileRootDir: coqFileRootDir,
                openaiApiKey: wsConfig.openaiApiKey,
                proofAttemsPerOneTheorem: wsConfig.proofAttemsPerOneTheorem,
                maxNumberOfTokens: wsConfig.maxNumberOfTokens,
                logAttempts: wsConfig.logAttempts,
                logFolderPath: wsConfig.logFolderPath === "None" ? null : wsConfig.logFolderPath,
                proofHolesCreateAux: wsConfig.proofHolesCreateAux, 
                gptModel: wsConfig.gptModel,
                proveAllOnStartup: wsConfig.startProvingAfterInit
            };
        } catch (error) {
            console.error(error);
            return undefined;
        }
    }

    export function checkRequirements(config: CoqpilotConfig): void {
        const nullableParams = [
            "logFolderPath"
        ];
        for (const [key, value] of Object.entries(config)) {
            if (!nullableParams.includes(key) && (value === undefined || value === null)) { 
                throw new Error(`Configuration parameter ${key} is undefined or null.`);
            }
        }
    }

    export function getLlm(config: CoqpilotConfig): LLMInterface {
        if (config.gptModel === OtherModels.MOCK) {
            return new MockLlmPrompt();
        } else if (Object.values(GptModel).map(v => v.toString()).includes(config.gptModel)) {
            return new GPT35(config.openaiApiKey, 3, config.gptModel);
        } else {
            throw new Error(`Unknown model ${config.gptModel}`);
        }
    }
}

/* eslint-disable @typescript-eslint/naming-convention */
export enum GptModel {
    GPT35 = 'gpt-3.5-turbo-0301',
    GPT4 = 'gpt-4',
    GPT4_0314 = 'gpt-4-0314',
    GPT4_0613 = 'gpt-4-0613',
    GPT4_32k = 'gpt-4-32k',
    GPT4_32k_0314 = 'gpt-4-32k-0314',
    GPT4_32k_0613 = 'gpt-4-32k-0613',
    GPT35_TURBO = 'gpt-3.5-turbo',
    GPT35_TURBO_16k = 'gpt-3.5-turbo-16k',
    GPT35_TURBO_0613 = 'gpt-3.5-turbo-0613',
    GPT35_TURBO_16k_0613 = 'gpt-3.5-turbo-16k-0613'
}

export enum OtherModels {
    MOCK = 'Mock'
}