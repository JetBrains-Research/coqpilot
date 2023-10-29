import { CoqpilotConfig, OtherModels, GptModel } from "../../extension/config";

export function mockConfig(): CoqpilotConfig {
    return {
        openaiApiKey: "None",
        proofAttemsPerOneTheorem: 2,
        maxNumberOfTokens: 1,
        logAttempts: false,
        logFolderPath: "None",
        gptModel: OtherModels.MOCK, 
        parseFileOnInit: false,
        parseFileOnEditorChange: false,
        coqLspPath: "coq-lsp"
    };
}

export function mockConfigRealGpt(apikey: string): CoqpilotConfig {
    return {
        openaiApiKey: apikey,
        proofAttemsPerOneTheorem: 25,
        maxNumberOfTokens: 40000,
        logAttempts: false,
        logFolderPath: "None",
        gptModel: GptModel.GPT35,
        parseFileOnInit: false,
        parseFileOnEditorChange: false,
        coqLspPath: "coq-lsp"
    };
}