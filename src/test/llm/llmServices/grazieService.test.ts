import { expect } from "earl";

import { GrazieService } from "../../../llm/llmServices/grazie/grazieService";
import { GrazieUserModelParams } from "../../../llm/userModelParams";

import { testIf } from "../../commonTestFunctions/conditionalTest";
import { testModelId } from "../llmSpecificTestUtils/constants";
import { testLLMServiceCompletesAdmitFromFile } from "../llmSpecificTestUtils/testAdmitCompletion";

suite("[LLMService] Test `GrazieService`", function () {
    const apiKey = process.env.GRAZIE_API_KEY;
    const choices = 15;
    const inputFile = ["small_document.v"];

    testIf(
        apiKey !== undefined,
        "`GRAZIE_API_KEY` is not specified",
        this.title,
        `Simple generation: 1 request, ${choices} choices`,
        async () => {
            const userParams: GrazieUserModelParams = {
                modelId: testModelId,
                modelName: "openai-gpt-4",
                apiKey: apiKey!,
                maxTokensToGenerate: 2000,
                tokensLimit: 4000,
            };
            const grazieService = new GrazieService();
            await testLLMServiceCompletesAdmitFromFile(
                grazieService,
                userParams,
                inputFile,
                choices
            );
        }
    )?.timeout(6000);

    test("Resolve parameters with predefined `maxTokensToGenerate`", () => {
        const userParams: GrazieUserModelParams = {
            modelId: testModelId,
            modelName: "openai-gpt-4",
            apiKey: "",
            maxTokensToGenerate: 6666, // should be overriden by GrazieService
            tokensLimit: 4000,
        };
        const grazieService = new GrazieService();
        try {
            const resolvedParams = grazieService.resolveParameters(userParams);
            expect(resolvedParams.maxTokensToGenerate).toEqual(
                grazieService.maxTokensToGeneratePredefined
            );
        } finally {
            grazieService.dispose();
        }
    });
});
