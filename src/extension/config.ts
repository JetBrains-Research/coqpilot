import { GPT35 } from '../coqLlmInteraction/gpt35';
import { SingleTacticSolver } from '../coqLlmInteraction/singleTacticSolver';
import { LLMAdapter } from '../coqLlmInteraction/llmAdapter';
import { MockLlmPrompt } from '../test/mock/mockllm';
import { LLMInterface } from '../coqLlmInteraction/llmInterface';
import * as vscode from 'vscode';
import logger from "./logger";

export interface CoqpilotConfig {
    openaiApiKey: string;
    proofAttemsPerOneTheorem: number;
    maxNumberOfTokens: number;
    logAttempts: boolean;
    logFolderPath: string | null;
    gptModel: string;
    parseFileOnEditorChange: boolean;
    parseFileOnInit: boolean;
    coqLspPath: string;
    useGpt: boolean;
    extraCommandsList: string[];
}

export class CoqpilotConfigWrapper {
    private _config: CoqpilotConfig;
    get config(): CoqpilotConfig {
        this._config = CoqpilotConfig.create(
            vscode.workspace.getConfiguration('coqpilot')
        );
        CoqpilotConfig.checkRequirements(this._config);
        logger.info("Successfully updated config: " + JSON.stringify(this._config));

        return this._config;
    }

    constructor(conf: CoqpilotConfig | undefined = undefined) {
        this._config = conf ?? CoqpilotConfig.create(
            vscode.workspace.getConfiguration('coqpilot')
        )!;
        CoqpilotConfig.checkRequirements(this._config);
        logger.info("Successfully created config.");
    }
}

export namespace CoqpilotConfig {
    export function getNew() {
        return new CoqpilotConfigWrapper();
    }

    export function create(
        wsConfig: any
    ): CoqpilotConfig | undefined {
        try {
            return {
                openaiApiKey: wsConfig.openaiApiKey,
                proofAttemsPerOneTheorem: wsConfig.proofAttemsPerOneTheorem,
                maxNumberOfTokens: wsConfig.maxNumberOfTokens,
                logAttempts: wsConfig.logAttempts,
                logFolderPath: wsConfig.logFolderPath === "None" ? null : wsConfig.logFolderPath,
                gptModel: wsConfig.gptModel,
                parseFileOnEditorChange: wsConfig.parseFileOnEditorChange,
                parseFileOnInit: wsConfig.parseFileOnInit, 
                coqLspPath: wsConfig.coqLspPath, 
                useGpt: wsConfig.useGpt, 
                extraCommandsList: preprocessExtraCommands(wsConfig.extraCommandsList)
            };
        } catch (error) {
            console.error(error);
            return undefined;
        }
    }

    function preprocessExtraCommands(commands: string[]): string[] {
        // If the command does not end with a dot, add it
        return commands.map((command) => {
            if (command.endsWith(".")) {
                return command;
            } else {
                return command + ".";
            }
        });
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

    export function getLlm(configWrapped: CoqpilotConfigWrapper): LLMInterface {
        const config = configWrapped.config;
        if (config.gptModel === OtherModels.MOCK) {
            return new MockLlmPrompt();
        } else {
            let gptModel: LLMInterface | null = null; 
            if (config.useGpt) {
                if (Object.values(GptModel).map(v => v.toString()).includes(config.gptModel)) {
                    gptModel = new GPT35(configWrapped, 3);
                } else {
                    throw new Error(`Unknown model ${config.gptModel}`);
                }
            }
            
            const simplestModel = new SingleTacticSolver(configWrapped);
            
            const allModels = [
                gptModel, simplestModel
            ].filter((model) => model !== null);
            
            return new LLMAdapter(allModels);
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