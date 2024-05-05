import { expect } from "earl";

import { theoremToChatItem } from "../../../../llm/llmServices/utils/chatFactory";
import { ChatTokensFitter } from "../../../../llm/llmServices/utils/chatTokensFitter";
import { chatItemToContent } from "../../../../llm/llmServices/utils/chatUtils";

import { Theorem } from "../../../../coqParser/parsedTypes";
import { parseTheoremsFromCoqFile } from "../../../commonTestFunctions/coqFileParser";
import {
    approxCalculateTokens,
    calculateTokensViaTikToken,
} from "../../llmSpecificTestUtils/calculateTokens";
import { gptTurboModelName } from "../../llmSpecificTestUtils/constants";

suite("[LLMService-s utils] ChatTokensFitter test", () => {
    async function readTwoTheorems(): Promise<Theorem[]> {
        const twoTheorems = await parseTheoremsFromCoqFile([
            "small_document.v",
        ]);
        expect(twoTheorems).toHaveLength(2);
        return twoTheorems;
    }

    interface TestParams {
        modelName?: string;
        newMessageMaxTokens: number;
        tokensLimit: number;
        systemMessage: string;
        completionTarget: string;
        contextTheorems: Theorem[];
    }

    function countTheoremsPickedFromContext(testParams: TestParams): number {
        const fitter = new ChatTokensFitter(
            testParams.newMessageMaxTokens,
            testParams.tokensLimit,
            testParams.modelName
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

    test("No theorems", () => {
        const fittedTheoremsNumber = countTheoremsPickedFromContext({
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
            gptTurboModelName
        );
        const theoremProof = twoTheorems[0].proof?.onlyText() ?? "";
        const proofTokens = calculateTokensViaTikToken(
            theoremProof,
            gptTurboModelName
        );
        const fittedTheoremsNumber = countTheoremsPickedFromContext({
            modelName: gptTurboModelName,
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
            gptTurboModelName
        );
        const approxTokens = approxCalculateTokens(shortText);
        expect(tiktokenTokens).toBeCloseTo(approxTokens, 2);
    });

    test("Test if two tokenizers are similar: long text", () => {
        const tiktokenTokens = calculateTokensViaTikToken(
            longText,
            gptTurboModelName
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
            newMessageMaxTokens,
            1000000,
            modelName
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
            gptTurboModelName
        );
        const newMessageMaxTokens = 100;
        expect(
            estimateTokensWithFitter(
                gptTurboModelName,
                longText,
                newMessageMaxTokens
            )
        ).toEqual(tiktokenTokens + newMessageMaxTokens);
    });
});
