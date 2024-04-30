import { expect } from "earl";
import * as tmp from "tmp";

import { GrazieService } from "../../../llm/llmServices/grazie/grazieService";
import { GrazieUserModelParams } from "../../../llm/userModelParams";

import { testIf } from "../../commonTestFunctions";
import { testLLMServiceCompletesAdmitFromFile } from "../testUtils/commonTestFunctions";

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
                modelName: "openai-gpt-4",
                apiKey: apiKey!,
                newMessageMaxTokens: 2000,
                tokensLimit: 4000,
            };
            const grazieService = new GrazieService(tmp.fileSync().name);
            await testLLMServiceCompletesAdmitFromFile(
                grazieService,
                userParams,
                inputFile,
                choices
            );
        }
    )?.timeout(6000);

    test("Resolve parameters with constant `newMessageMaxTokens`", () => {
        const userParams: GrazieUserModelParams = {
            modelName: "openai-gpt-4",
            apiKey: "",
            newMessageMaxTokens: 6666, // should be overriden by GrazieService
            tokensLimit: 4000,
        };
        const grazieService = new GrazieService(tmp.fileSync().name);
        try {
            const resolvedParams = grazieService.resolveParameters(userParams);
            expect(resolvedParams.newMessageMaxTokens).toEqual(
                grazieService.newMessageMaxTokens
            );
        } finally {
            grazieService.dispose();
        }
    });
});
