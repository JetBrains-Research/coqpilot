import * as tmp from "tmp";

import { OpenAiService } from "../../../llm/llmServices/openai/openAiService";
import { OpenAiUserModelParams } from "../../../llm/userModelParams";

import { color, testIf } from "../../commonTestFunctions";
import { testLLMServiceCompletesAdmitFromFile } from "../testUtils/commonTestFunctions";

const suiteName = "[LLMService] Test `OpenAiService`";

suite(suiteName, () => {
    const apiKey = process.env.OPENAI_API_KEY;
    if (apiKey === undefined) {
        console.warn(
            `${color("WARNING", "yellow")}: suite "${suiteName}" will be skipped, because \`OPENAI_API_KEY\` is not specified`
        );
    }
    const choices = 15;
    const inputFileName = "small_document.v";

    testIf(
        apiKey !== undefined,
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
                inputFileName,
                choices
            );
        }
    );
});
