import { expect } from "earl";
import * as path from "path";
import { TiktokenModel, encoding_for_model } from "tiktoken";

import { theoremToChatItem } from "../../../../llm/llmServices/utils/chatFactory";
import { ChatTokensFitter } from "../../../../llm/llmServices/utils/chatTokensFitter";
import { chatItemToContent } from "../../../../llm/llmServices/utils/chatUtils";

import { parseCoqFile } from "../../../../coqParser/parseCoqFile";
import { Theorem } from "../../../../coqParser/parsedTypes";
import { Uri } from "../../../../utils/uri";
import {
    createCoqLspClient,
    getResourceFolder,
} from "../../../commonTestFunctions";

suite("[LLMService-s utils] ChatTokensFitter test", () => {
    function calculateTokensViaTikToken(
        text: string,
        model: TiktokenModel
    ): number {
        const encoder = encoding_for_model(model);
        const tokens = encoder.encode(text).length;
        encoder.free();
        return tokens;
    }

    function approxCalculateTokens(text: string): number {
        return (text.length / 4) >> 0;
    }

    async function parseTheoremsFromCoqFile(
        resourcePath: string[],
        projectRootPath?: string[]
    ): Promise<Theorem[]> {
        const filePath = path.join(getResourceFolder(), ...resourcePath);
        const rootDir = path.join(
            getResourceFolder(),
            ...(projectRootPath ?? [])
        );

        const fileUri = Uri.fromPath(filePath);
        const client = createCoqLspClient(rootDir);

        await client.openTextDocument(fileUri);
        const document = await parseCoqFile(fileUri, client);
        await client.closeTextDocument(fileUri);

        return document;
    }

    async function readTwoTheorems(): Promise<Theorem[]> {
        const twoTheorems = await parseTheoremsFromCoqFile([
            "small_document.v",
        ]);
        expect(twoTheorems).toHaveLength(2);
        return twoTheorems;
    }

    interface TestParams {
        model: string;
        newMessageMaxTokens: number;
        tokensLimit: number;
        systemMessage: string;
        completionTarget: string;
        contextTheorems: Theorem[];
    }

    function countTheoremsPickedFromContext(testParams: TestParams): number {
        const fitter = new ChatTokensFitter(
            testParams.model,
            testParams.newMessageMaxTokens,
            testParams.tokensLimit
        );
        try {
            fitter.fitRequiredMessage({
                role: "system",
                content: testParams.systemMessage,
            });
            fitter.fitRequiredMessage({
                role: "user",
                content: testParams.completionTarget,
            });

            const fittedTheorems = fitter.fitOptionalObjects(
                testParams.contextTheorems,
                (theorem) => chatItemToContent(theoremToChatItem(theorem))
            );
            return fittedTheorems.length;
        } finally {
            fitter.dispose();
        }
    }

    const gptTurboModel = "gpt-3.5-turbo-0301";

    test("No theorems", () => {
        const fittedTheoremsNumber = countTheoremsPickedFromContext({
            model: "openai-gpt",
            newMessageMaxTokens: 100,
            tokensLimit: 1000,
            systemMessage: "You are a friendly assistant",
            completionTarget: "doesn't matter",
            contextTheorems: [],
        });
        expect(fittedTheoremsNumber).toEqual(0);
    });

    test("Required messages do not fit", async () => {
        const twoTheorems = await readTwoTheorems();
        expect(() => {
            countTheoremsPickedFromContext({
                model: "openai-gpt",
                newMessageMaxTokens: 1000,
                tokensLimit: 1000,
                systemMessage: "You are a friendly assistant",
                completionTarget: "doesn't matter",
                contextTheorems: twoTheorems,
            });
        }).toThrow();
    });

    test("Two theorems, no overflow", async () => {
        const twoTheorems = await readTwoTheorems();
        const fittedTheoremsNumber = countTheoremsPickedFromContext({
            model: "openai-gpt",
            newMessageMaxTokens: 1000,
            tokensLimit: 10000,
            systemMessage: "You are a friendly assistant",
            completionTarget: "doesn't matter",
            contextTheorems: twoTheorems,
        });
        expect(fittedTheoremsNumber).toEqual(2);
    });

    test("Two theorems, overflow after first", async () => {
        const twoTheorems = await readTwoTheorems();
        const statementTokens = approxCalculateTokens(twoTheorems[0].statement);
        const theoremProof = twoTheorems[0].proof?.onlyText() ?? "";
        const proofTokens = approxCalculateTokens(theoremProof);
        const fittedTheoremsNumber = countTheoremsPickedFromContext({
            model: "invalid-model",
            newMessageMaxTokens: 1000,
            tokensLimit: 1000 + statementTokens + proofTokens,
            systemMessage: "",
            completionTarget: "",
            contextTheorems: twoTheorems,
        });
        expect(fittedTheoremsNumber).toEqual(1);
    });

    test("Two theorems, overflow almost before first", async () => {
        const twoTheorems = await readTwoTheorems();
        const statementTokens = approxCalculateTokens(twoTheorems[0].statement);
        const theoremProof = twoTheorems[0].proof?.onlyText() ?? "";
        const proofTokens = approxCalculateTokens(theoremProof);
        const fittedTheoremsNumber = countTheoremsPickedFromContext({
            model: "invalid-model",
            newMessageMaxTokens: 1000,
            tokensLimit: 1000 + statementTokens + proofTokens - 1,
            systemMessage: "",
            completionTarget: "",
            contextTheorems: twoTheorems,
        });
        expect(fittedTheoremsNumber).toEqual(0);
    });

    test("Two theorems, overflow after first with tiktoken", async () => {
        const twoTheorems = await readTwoTheorems();
        const statementTokens = calculateTokensViaTikToken(
            twoTheorems[0].statement,
            gptTurboModel
        );
        const theoremProof = twoTheorems[0].proof?.onlyText() ?? "";
        const proofTokens = calculateTokensViaTikToken(
            theoremProof,
            gptTurboModel
        );
        const fittedTheoremsNumber = countTheoremsPickedFromContext({
            model: gptTurboModel,
            newMessageMaxTokens: 1000,
            tokensLimit: 1000 + statementTokens + proofTokens,
            systemMessage: "",
            completionTarget: "",
            contextTheorems: twoTheorems,
        });
        expect(fittedTheoremsNumber).toEqual(1);
    });

    const shortText = "This is a test text";
    const longText =
        "Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.";

    test("Test if two tokenizers are similar: short text", () => {
        const tiktokenTokens = calculateTokensViaTikToken(
            shortText,
            gptTurboModel
        );
        const approxTokens = approxCalculateTokens(shortText);
        expect(tiktokenTokens).toBeCloseTo(approxTokens, 2);
    });

    test("Test if two tokenizers are similar: long text", () => {
        const tiktokenTokens = calculateTokensViaTikToken(
            longText,
            gptTurboModel
        );
        const approxTokens = approxCalculateTokens(longText);
        expect(tiktokenTokens).toBeCloseTo(approxTokens, 20);
    });

    function estimateTokensWithFitter(
        modelName: string,
        text: string,
        newMessageMaxTokens: number
    ): number {
        const fitter = new ChatTokensFitter(
            modelName,
            newMessageMaxTokens,
            1000000
        );
        try {
            fitter.fitRequiredMessage({
                role: "user", // doesn't matter
                content: text,
            });
            return fitter.estimateTokens();
        } finally {
            fitter.dispose();
        }
    }

    test("Test `estimateTokens`", () => {
        const tiktokenTokens = calculateTokensViaTikToken(
            longText,
            gptTurboModel
        );
        const newMessageMaxTokens = 100;
        expect(
            estimateTokensWithFitter(
                gptTurboModel,
                longText,
                newMessageMaxTokens
            )
        ).toEqual(tiktokenTokens + newMessageMaxTokens);
    });
});
