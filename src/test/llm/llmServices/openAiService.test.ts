import { OpenAiService } from "../../../llm/llmServices/openai/openAiService";
import { OpenAiUserModelParams } from "../../../llm/userModelParams";

import { testIf } from "../../commonTestFunctions/conditionalTest";
import { testModelId } from "../llmSpecificTestUtils/constants";
import { testLLMServiceCompletesAdmitFromFile } from "../llmSpecificTestUtils/testAdmitCompletion";

suite("[LLMService] Test `OpenAiService`", function () {
    const apiKey = process.env.OPENAI_API_KEY;
    const choices = 15;
    const inputFile = ["small_document.v"];

    testIf(
        apiKey !== undefined,
        "`OPENAI_API_KEY` is not specified",
        this.title,
        `Simple generation: 1 request, ${choices} choices`,
        async () => {
            const userParams: OpenAiUserModelParams = {
                modelId: testModelId,
                modelName: "gpt-3.5-turbo-0301",
                temperature: 1,
                apiKey: apiKey!,
                newMessageMaxTokens: 2000,
                tokensLimit: 4000,
            };
            const openAiService = new OpenAiService();
            await testLLMServiceCompletesAdmitFromFile(
                openAiService,
                userParams,
                inputFile,
                choices
            );
        }
    );
});
