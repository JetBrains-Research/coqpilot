import { CoqpilotConfig, OtherModels, GptModel } from "../../extension/config";
import { Profile } from "../../coqLlmInteraction/grazie/chatInstance";
import { ConfigWrapperInterface } from "../../extension/config";


export class MockConfigWrapper implements ConfigWrapperInterface {
    config: CoqpilotConfig;

    constructor(config: CoqpilotConfig) {
        this.config = config;
    }
}

const defaultConfig = {
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
    shuffleHoles: false, 
    lmStudioPort: "None", 
    useLmStudio: false
};

export function mockConfig(): CoqpilotConfig {
    return {
        ...defaultConfig
    };
}

export function mockConfigRealGpt(apikey: string): CoqpilotConfig {
    return {
        ...defaultConfig,
        openaiApiKey: apikey,
        proofAttemsPerOneTheorem: 25,
        maxNumberOfTokens: 40000,
        gptModel: GptModel.GPT35,
        coqLspPath: "coq-lsp",
    };
}

export function simpleSolverMockConfig(tactics: string[]): CoqpilotConfig {
    return {
        ...defaultConfig,
        gptModel: GptModel.GPT35, 
        coqLspPath: "coq-lsp",
        extraCommandsList: tactics, 
    };
}