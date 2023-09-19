import { CoqpilotConfig, OtherModels } from "../../extension/config";
import * as path from 'path';

export function mockConfig(coqFilePath: string): CoqpilotConfig | undefined {
    return {
        coqFilePath: coqFilePath,
        coqFileRootDir: path.dirname(coqFilePath),
        openaiApiKey: "None",
        proofAttemsPerOneTheorem: 1,
        maxNumberOfTokens: 1,
        logAttempts: false,
        logFolderPath: "None",
        proofHolesCreateAux: false,
        gptModel: OtherModels.MOCK, 
        proveAllOnStartup: false
    };
} 