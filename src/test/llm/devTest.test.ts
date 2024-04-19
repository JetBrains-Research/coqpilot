import { expect } from "earl";
import * as path from "path";

import { PredefinedProofsModelParams } from "../../llm/llmServices/modelParams";
import {
    FromChatGenerationRequest,
    RequestsLogger,
} from "../../llm/llmServices/utils/requestsLogger/requestsLogger";

suite("LLM Dev Test", () => {
    test("Dev test", async () => {
        const root: string = path.join(__dirname, "../../../");
        const devTestDir = path.join(root, "devTest/");
        const filePath = path.join(devTestDir, "predefinedLogs.txt");

        const predefinedProofs = [
            "intros.",
            "reflexivity.",
            "auto.",
            "assumption. intros.",
            "left. reflexivity.",
        ];
        const params: PredefinedProofsModelParams = {
            tactics: predefinedProofs,
            modelName: "test model",
            systemPrompt: "hi system",
            newMessageMaxTokens: 10000,
            tokensLimit: 1000000,
            multiroundProfile: {
                maxRoundsNumber: 1,
                proofFixChoices: 1,
                proofFixPrompt: "fix it",
            },
        };
        const request: FromChatGenerationRequest = {
            chat: [
                {
                    role: "system",
                    content: "hello from system!",
                },
                {
                    role: "user",
                    content: "hello from user!\nI love multiline!",
                },
                {
                    role: "assistant",
                    content: "hello from assistant!",
                },
            ],
            estimatedTokens: 100,
            params: params,
            choices: 2,
        };
        const generatedProofs = ["auto.\nintro.", "auto."];

        const debug = true;
        const requestLogger = new RequestsLogger(filePath, debug);
        requestLogger.logRequestSucceeded(request, generatedProofs);
        requestLogger.logRequestSucceeded(request, generatedProofs);
        requestLogger.logRequestFailed(request, Error("network failed"));
        requestLogger.logRequestFailed(
            request,
            Error("tokens limit exceeded\nunfortunately, many times")
        );
        const records = requestLogger.readLogs();
        console.log(`PARSED RECORDS:\n${records}\n`);
        expect(records.length).toEqual(debug ? 4 : 3);
    });
});
