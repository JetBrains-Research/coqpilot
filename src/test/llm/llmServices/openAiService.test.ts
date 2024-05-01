import * as tmp from "tmp";

import { OpenAiService } from "../../../llm/llmServices/openai/openAiService";
import { OpenAiUserModelParams } from "../../../llm/userModelParams";

import { testIf } from "../../commonTestFunctions/conditionalTest";
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
                modelName: "gpt-3.5-turbo-0301",
                temperature: 1,
                apiKey: apiKey!,
                newMessageMaxTokens: 2000,
                tokensLimit: 4000,
            };
            const openAiService = new OpenAiService(tmp.fileSync().name);
            await testLLMServiceCompletesAdmitFromFile(
                openAiService,
                userParams,
                inputFile,
                choices
            );
        }
    );
});
