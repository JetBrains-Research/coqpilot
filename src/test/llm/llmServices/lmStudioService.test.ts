import * as tmp from "tmp";

import { LMStudioService } from "../../../llm/llmServices/lmStudio/lmStudioService";
import { LMStudioUserModelParams } from "../../../llm/userModelParams";

import { testIf } from "../../commonTestFunctions/conditionalTest";
import { testLLMServiceCompletesAdmitFromFile } from "../llmSpecificTestUtils/testAdmitCompletion";

suite("[LLMService] Test `LMStudioService`", function () {
    const lmStudioPort = process.env.LMSTUDIO_PORT;
    const choices = 15;
    const inputFile = ["small_document.v"];

    testIf(
        lmStudioPort !== undefined,
        "`LMSTUDIO_PORT` is not specified",
        this.title,
        `Simple generation: 1 request, ${choices} choices`,
        async () => {
            const userParams: LMStudioUserModelParams = {
                modelName: "lm-studio",
                temperature: 1,
                port: parseInt(lmStudioPort!),
                newMessageMaxTokens: 2000,
                tokensLimit: 4000,
            };
            const lmStudioService = new LMStudioService(tmp.fileSync().name);
            await testLLMServiceCompletesAdmitFromFile(
                lmStudioService,
                userParams,
                inputFile,
                choices
            );
        }
    );
});
