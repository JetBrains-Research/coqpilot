import { CoqpilotConfig, OtherModels, GptModel } from "../../extension/config";
import * as path from 'path';

export function mockConfig(coqFilePath: string): CoqpilotConfig {
    return {
        coqFilePath: coqFilePath,
        coqFileRootDir: path.dirname(coqFilePath),
        openaiApiKey: "None",
        proofAttemsPerOneTheorem: 2,
        maxNumberOfTokens: 1,
        logAttempts: false,
        logFolderPath: "None",
        proofHolesCreateAux: false,
        gptModel: OtherModels.MOCK, 
        proveAllOnStartup: false
    };
} 

export function mockConfigRealGpt(coqFilePath: string, coqRoot: string, apikey: string): CoqpilotConfig {
    return {
        coqFilePath: coqFilePath,
        coqFileRootDir: coqRoot,
        openaiApiKey: apikey,
        proofAttemsPerOneTheorem: 25,
        maxNumberOfTokens: 40000,
        logAttempts: false,
        logFolderPath: "None",
        proofHolesCreateAux: false,
        gptModel: GptModel.GPT35,
        proveAllOnStartup: false
    };
}