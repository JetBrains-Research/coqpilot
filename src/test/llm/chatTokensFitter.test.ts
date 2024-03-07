import { expect } from "earl";
import * as path from "path";
import { TiktokenModel, encoding_for_model } from "tiktoken";

import { theoremToChatItem } from "../../llm/llmServices/utils/chatFactory";
import { ChatTokensFitter } from "../../llm/llmServices/utils/chatTokensFitter";
import { chatItemToContent } from "../../llm/llmServices/utils/chatUtils";

import { parseCoqFile } from "../../coqParser/parseCoqFile";
import { Theorem } from "../../coqParser/parsedTypes";
import { Uri } from "../../utils/uri";
import { createCoqLspClient, getResourceFolder } from "../commonTestFunctions";

suite("Chat tokens fitter tests", () => {
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

    async function getCoqDocument(
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

    function countTheoremsPickedFromContext(
        systemMessage: string,
        completionTarget: string,
        theorems: Theorem[],
        model: string,
        newMessageMaxTokens: number,
        tokensLimit: number
    ): number {
        const fitter = new ChatTokensFitter(
            model,
            newMessageMaxTokens,
            tokensLimit
        );

        fitter.fitRequiredMessage({
            role: "system",
            content: systemMessage,
        });

        fitter.fitRequiredMessage({
            role: "user",
            content: completionTarget,
        });

        const fittedTheorems = fitter.fitOptionalObjects(theorems, (theorem) =>
            chatItemToContent(theoremToChatItem(theorem))
        );

        return fittedTheorems.length;
    }

    test("Empty theorems array", async () => {
        const theorems: Theorem[] = [];
        const answer = countTheoremsPickedFromContext(
            "You are a friendly assistant",
            "doesn't matter",
            theorems,
            "openai-gpt",
            100,
            1000
        );

        expect(answer).toEqual(0);
    });

    test("Two theorems, but overflow", async () => {
        const theorems: Theorem[] = await getCoqDocument(["small_document.v"]);
        expect(() => {
            countTheoremsPickedFromContext(
                "You are a friendly assistant",
                "doesn't matter",
                theorems,
                "openai-gpt",
                1000,
                1000
            );
        }).toThrow();
    });

    test("Two theorems, no overflow", async () => {
        const theorems: Theorem[] = await getCoqDocument(["small_document.v"]);
        const answer = countTheoremsPickedFromContext(
            "You are a friendly assistant",
            "doesn't matter",
            theorems,
            "openai-gpt",
            1000,
            10000
        );

        expect(answer).toEqual(2);
    });

    test("Two theorems, overflow after first", async () => {
        const theorems: Theorem[] = await getCoqDocument(["small_document.v"]);

        const statementTokens = approxCalculateTokens(theorems[0].statement);
        const theoremProof = theorems[0].proof?.onlyText() ?? "";
        const proofTokens = approxCalculateTokens(theoremProof);
        const answer = countTheoremsPickedFromContext(
            "",
            "",
            theorems,
            "invalid-model",
            1000,
            1000 + statementTokens + proofTokens
        );

        expect(answer).toEqual(1);
    });

    test("Two theorems, overflow almost before first", async () => {
        const theorems: Theorem[] = await getCoqDocument(["small_document.v"]);

        const statementTokens = approxCalculateTokens(theorems[0].statement);
        const theoremProof = theorems[0].proof?.onlyText() ?? "";
        const proofTokens = approxCalculateTokens(theoremProof);

        const answer = countTheoremsPickedFromContext(
            "",
            "",
            theorems,
            "invalid-model",
            1000,
            1000 + statementTokens + proofTokens - 1
        );

        expect(answer).toEqual(0);
    });

    test("Two theorems, overflow after first with tiktoken", async () => {
        const theorems: Theorem[] = await getCoqDocument(["small_document.v"]);
        const model = "gpt-3.5-turbo-0301";

        const statementTokens = calculateTokensViaTikToken(
            theorems[0].statement,
            model
        );
        const theoremProof = theorems[0].proof?.onlyText() ?? "";
        const proofTokens = calculateTokensViaTikToken(theoremProof, model);
        const answer = countTheoremsPickedFromContext(
            "",
            "",
            theorems,
            model,
            1000,
            1000 + statementTokens + proofTokens
        );

        expect(answer).toEqual(1);
    });

    test("Test if two tokenizers are similar: Small text", async () => {
        const model = "gpt-3.5-turbo-0301";

        const text = "This is a test text";
        const tokens1 = calculateTokensViaTikToken(text, model);
        const tokens2 = approxCalculateTokens(text);

        expect(tokens1).toBeCloseTo(tokens2, 2);
    });

    test("Test if two tokenizers are similar: Big text", async () => {
        const model = "gpt-3.5-turbo-0301";

        const text =
            "Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.";
        const tokens1 = calculateTokensViaTikToken(text, model);
        const tokens2 = approxCalculateTokens(text);

        expect(tokens1).toBeCloseTo(tokens2, 20);
    });
});
