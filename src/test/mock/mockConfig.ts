import { CoqpilotConfig, OtherModels, GptModel } from "../../extension/config";
import { Profile } from "../../coqLlmInteraction/grazie/chatInstance";
import { ConfigWrapperInterface } from "../../extension/config";


export class MockConfigWrapper implements ConfigWrapperInterface {
    config: CoqpilotConfig;

    constructor(config: CoqpilotConfig) {
        this.config = config;
    }
}

export function mockConfig(): CoqpilotConfig {
    return {
        openaiApiKey: "None",
        grazieApiKey: "None",
        proofAttemsPerOneTheorem: 2,
        maxNumberOfTokens: 1,
        logAttempts: false,
        logFolderPath: "None",
        gptModel: OtherModels.MOCK, 
        grazieModel: Profile.NONE,
        parseFileOnInit: false,
        parseFileOnEditorChange: false,
        coqLspPath: process.env.COQ_LSP_PATH || "coq-lsp",
        extraCommandsList: [], 
        shuffleHoles: false
    };
}

export function mockConfigRealGpt(apikey: string): CoqpilotConfig {
    return {
        openaiApiKey: apikey,
        grazieApiKey: "None",
        proofAttemsPerOneTheorem: 25,
        maxNumberOfTokens: 40000,
        logAttempts: false,
        logFolderPath: "None",
        gptModel: GptModel.GPT35,
        grazieModel: Profile.NONE,
        parseFileOnInit: false,
        parseFileOnEditorChange: false,
        coqLspPath: "coq-lsp",
        extraCommandsList: [], 
        shuffleHoles: false
    };
}

export function simpleSolverMockConfig(tactics: string[]): CoqpilotConfig {
    return {
        openaiApiKey: "None",
        grazieApiKey: "None",
        proofAttemsPerOneTheorem: 2,
        maxNumberOfTokens: 1,
        logAttempts: false,
        logFolderPath: "None",
        gptModel: GptModel.GPT35, 
        grazieModel: Profile.NONE,
        parseFileOnInit: false,
        parseFileOnEditorChange: false,
        coqLspPath: "coq-lsp",
        extraCommandsList: tactics, 
        shuffleHoles: false
    };
}