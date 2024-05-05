import { LMStudioService } from "../../../llm/llmServices/lmStudio/lmStudioService";
import { LMStudioUserModelParams } from "../../../llm/userModelParams";

import { testIf } from "../../commonTestFunctions/conditionalTest";
import { testModelId } from "../llmSpecificTestUtils/constants";
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
                modelId: testModelId,
                temperature: 1,
                port: parseInt(lmStudioPort!),
                maxTokensToGenerate: 2000,
                tokensLimit: 4000,
            };
            const lmStudioService = new LMStudioService();
            await testLLMServiceCompletesAdmitFromFile(
                lmStudioService,
                userParams,
                inputFile,
                choices
            );
        }
    );
});
