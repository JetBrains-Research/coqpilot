import { expect } from "earl";

import { ChatHistory, ChatMessage } from "../../../../llm/llmServices/chat";
import { ProofVersion } from "../../../../llm/llmServices/llmService";
import { ModelParams } from "../../../../llm/llmServices/modelParams";
import {
    buildChat,
    buildPreviousProofVersionsChat,
    buildProofFixChat,
    buildProofGenerationChat,
    buildTheoremsChat,
    createProofFixMessage,
    validateChat,
} from "../../../../llm/llmServices/utils/chatFactory";
import {
    ItemizedChat,
    UserAssistantChatItem,
    chatItemToContent,
    itemizedChatToHistory,
} from "../../../../llm/llmServices/utils/chatUtils";
import { ProofGenerationContext } from "../../../../llm/proofGenerationContext";

import { Theorem } from "../../../../coqParser/parsedTypes";
import { parseTheoremsFromCoqFile } from "../../../commonTestFunctions/coqFileParser";
import { calculateTokensViaTikToken } from "../../llmSpecificTestUtils/calculateTokens";
import { gptTurboModel } from "../../llmSpecificTestUtils/constants";

/*
 * Note: if in the future some of the tests will act against experiments with chats,
 * feel free to make them simplier. So far, they just check the current specification.
 */
suite("[LLMService-s utils] Building chats test", () => {
    async function readTheorems(): Promise<Theorem[]> {
        const theorems = await parseTheoremsFromCoqFile([
            "build_chat_theorems.v",
        ]);
        expect(theorems).toHaveLength(3);
        return theorems;
    }

    interface TestMessages {
        systemMessage: ChatMessage;

        // user messages
        plusTheoremStatement: ChatMessage;
        plusAssocTheoremStatement: ChatMessage;
        theoremToCompleteStatement: ChatMessage;

        // assistant messages
        plusTheoremProof: ChatMessage;
        plusAssocTheoremProof: ChatMessage;

        proofGenerationChat: ChatHistory;
    }

    interface TestTheorems {
        plusTheorem: Theorem;
        plusAssocTheorem: Theorem;
        theoremToComplete: Theorem;
    }

    async function buildTestData(): Promise<[TestTheorems, TestMessages]> {
        const [plusTheorem, plusAssocTheorem, theoremToComplete] =
            await readTheorems();
        expect(plusTheorem.proof).toBeTruthy();
        expect(plusAssocTheorem.proof).toBeTruthy();

        const messages = {
            systemMessage: {
                role: "system",
                content: "Generate proofs in Coq!",
            } as ChatMessage,
            plusTheoremStatement: {
                role: "user",
                content: plusTheorem.statement,
            } as ChatMessage,
            plusAssocTheoremStatement: {
                role: "user",
                content: plusAssocTheorem.statement,
            } as ChatMessage,
            theoremToCompleteStatement: {
                role: "user",
                content: theoremToComplete.statement,
            } as ChatMessage,

            plusTheoremProof: {
                role: "assistant",
                content: plusTheorem.proof!.onlyText(),
            } as ChatMessage,
            plusAssocTheoremProof: {
                role: "assistant",
                content: plusAssocTheorem.proof!.onlyText(),
            } as ChatMessage,
        };

        return [
            {
                plusTheorem: plusTheorem,
                plusAssocTheorem: plusAssocTheorem,
                theoremToComplete: theoremToComplete,
            },
            {
                ...messages,
                proofGenerationChat: [
                    messages.systemMessage,
                    messages.plusTheoremStatement,
                    messages.plusTheoremProof,
                    messages.plusAssocTheoremStatement,
                    messages.plusAssocTheoremProof,
                    messages.theoremToCompleteStatement,
                ],
            },
        ];
    }

    const misspelledProof: ProofVersion = {
        proof: "something???",
        diagnostic: "Bad input...",
    };
    const incorrectProof: ProofVersion = {
        proof: "auto.",
        diagnostic: "It does not finish proof...",
    };

    test("Test `validateChat`: valid chats", async () => {
        const [_, messages] = await buildTestData();

        const onlySystemMessageChat: ChatHistory = [messages.systemMessage];
        expect(validateChat(onlySystemMessageChat)).toEqual([true, "ok"]);

        const oneUserRequestChat: ChatHistory = [
            messages.systemMessage,
            messages.theoremToCompleteStatement,
        ];
        expect(validateChat(oneUserRequestChat)).toEqual([true, "ok"]);

        expect(validateChat(messages.proofGenerationChat)).toEqual([
            true,
            "ok",
        ]);
    });

    test("Test `validateChat`: invalid chats", async () => {
        const [_, messages] = await buildTestData();

        expect(validateChat([])).toEqual([
            false,
            "no system message at the chat start",
        ]);
        expect(validateChat([messages.theoremToCompleteStatement])).toEqual([
            false,
            "no system message at the chat start",
        ]);
        expect(
            validateChat([
                messages.systemMessage,
                messages.plusTheoremStatement,
                messages.systemMessage,
                messages.theoremToCompleteStatement,
            ])
        ).toEqual([false, "several system messages found"]);
        expect(
            validateChat([
                messages.systemMessage,
                messages.plusTheoremStatement,
                messages.plusTheoremStatement,
            ])
        ).toEqual([false, "two identical roles in a row"]);
        expect(
            validateChat([
                messages.systemMessage,
                messages.plusTheoremStatement,
                messages.plusTheoremProof,
            ])
        ).toEqual([
            false,
            "last message in the chat should be authored either by `user` or by `system`",
        ]);
    });

    test("Test `buildChat`", async () => {
        const [_, messages] = await buildTestData();

        expect(buildChat(messages.proofGenerationChat)).toEqual(
            messages.proofGenerationChat
        );
        expect(
            buildChat(
                messages.systemMessage,
                messages.plusTheoremStatement,
                messages.plusTheoremProof,
                messages.plusAssocTheoremStatement,
                messages.plusAssocTheoremProof,
                messages.theoremToCompleteStatement
            )
        ).toEqual(messages.proofGenerationChat);
        expect(
            buildChat(
                buildChat(messages.systemMessage),
                [messages.plusTheoremStatement, messages.plusTheoremProof],
                messages.theoremToCompleteStatement
            )
        ).toEqual([
            messages.systemMessage,
            messages.plusTheoremStatement,
            messages.plusTheoremProof,
            messages.theoremToCompleteStatement,
        ]);

        expect(() =>
            buildChat(messages.systemMessage, messages.systemMessage)
        ).toThrow();
    });

    test("Test chat-item wrappers", async () => {
        const [_, messages] = await buildTestData();

        const plusTheorem: UserAssistantChatItem = {
            userMessage: messages.plusTheoremStatement.content,
            assistantMessage: messages.plusTheoremProof.content,
        };
        const plusAssocTheorem: UserAssistantChatItem = {
            userMessage: messages.plusAssocTheoremStatement.content,
            assistantMessage: messages.plusAssocTheoremProof.content,
        };
        const itemizedHistory: ItemizedChat = [plusTheorem, plusAssocTheorem];

        expect(chatItemToContent(plusTheorem)).toEqual([
            messages.plusTheoremStatement.content,
            messages.plusTheoremProof.content,
        ]);
        expect(itemizedChatToHistory(itemizedHistory, true)).toEqual([
            messages.plusTheoremStatement,
            messages.plusTheoremProof,
            messages.plusAssocTheoremStatement,
            messages.plusAssocTheoremProof,
        ]);
        expect(itemizedChatToHistory(itemizedHistory, false)).toEqual([
            messages.plusTheoremProof,
            messages.plusTheoremStatement,
            messages.plusAssocTheoremProof,
            messages.plusAssocTheoremStatement,
        ]);
    });

    test("Test theorems chat builder", async () => {
        const [theorems, messages] = await buildTestData();
        const builtTheoremsChat = buildTheoremsChat([
            theorems.plusTheorem,
            theorems.plusAssocTheorem,
        ]);
        expect(builtTheoremsChat).toEqual([
            messages.plusTheoremStatement,
            messages.plusTheoremProof,
            messages.plusAssocTheoremStatement,
            messages.plusAssocTheoremProof,
        ]);
    });

    function proofVersionToChat(proofVersion: ProofVersion): ChatHistory {
        return [
            { role: "assistant", content: proofVersion.proof },
            {
                role: "user",
                content: `Proof is invalid, compiler diagnostic: ${proofVersion.diagnostic}`,
            },
        ];
    }

    test("Test previous-proof-versions chat builder", () => {
        const builtProofVersionsChat = buildPreviousProofVersionsChat([
            misspelledProof,
            incorrectProof,
        ]);
        expect(builtProofVersionsChat).toEqual([
            ...proofVersionToChat(misspelledProof),
            ...proofVersionToChat(incorrectProof),
        ]);
    });

    test("Test proof-generation-chat builder", async () => {
        const [theorems, messages] = await buildTestData();

        const proofGenerationContext: ProofGenerationContext = {
            completionTarget: theorems.theoremToComplete.statement,
            contextTheorems: [theorems.plusTheorem, theorems.plusAssocTheorem],
        };
        const unlimitedTokensModelParams: ModelParams = {
            modelName: gptTurboModel,
            systemPrompt: messages.systemMessage.content,
            newMessageMaxTokens: 100,
            tokensLimit: 100_000, // = super many, so all context will be used
            multiroundProfile: {
                maxRoundsNumber: 1,
                proofFixChoices: 3,
                proofFixPrompt: "Fix proof, please",
            },
        };
        const twoTheoremsChat = buildProofGenerationChat(
            proofGenerationContext,
            unlimitedTokensModelParams
        ).chat;
        expect(twoTheoremsChat).toEqual(messages.proofGenerationChat);

        const tokens = (text: string) => {
            return calculateTokensViaTikToken(text, gptTurboModel);
        };
        const limitedTokensModelParams: ModelParams = {
            ...unlimitedTokensModelParams,
            newMessageMaxTokens: 100,
            tokensLimit:
                100 +
                tokens(messages.systemMessage.content) +
                tokens(messages.theoremToCompleteStatement.content) +
                +tokens(messages.plusTheoremStatement.content) +
                tokens(messages.plusTheoremProof.content),
        };
        const oneTheoremChat = buildProofGenerationChat(
            proofGenerationContext,
            limitedTokensModelParams
        ).chat;
        expect(oneTheoremChat).toEqual([
            messages.systemMessage,
            messages.plusTheoremStatement,
            messages.plusTheoremProof,
            messages.theoremToCompleteStatement,
        ]);
    });

    test("Test proof-fix-chat builder", async () => {
        const [theorems, messages] = await buildTestData();

        const proofGenerationContext: ProofGenerationContext = {
            completionTarget: theorems.theoremToComplete.statement,
            contextTheorems: [theorems.plusTheorem, theorems.plusAssocTheorem],
        };
        const unlimitedTokensModelParams: ModelParams = {
            modelName: gptTurboModel,
            systemPrompt: messages.systemMessage.content,
            newMessageMaxTokens: 100,
            tokensLimit: 100_000, // = super many, so all context will be used
            multiroundProfile: {
                maxRoundsNumber: 1,
                proofFixChoices: 3,
                proofFixPrompt: "Fix proof, please: ${diagnostic}",
            },
        };
        const completeProofFixChat = buildProofFixChat(
            proofGenerationContext,
            [misspelledProof, incorrectProof],
            unlimitedTokensModelParams
        ).chat;
        expect(completeProofFixChat).toEqual([
            messages.systemMessage,
            messages.plusTheoremStatement,
            messages.plusTheoremProof,
            messages.plusAssocTheoremStatement,
            messages.plusAssocTheoremProof,
            messages.theoremToCompleteStatement,
            ...proofVersionToChat(misspelledProof),
            proofVersionToChat(incorrectProof)[0],
            {
                role: "user",
                content: createProofFixMessage(
                    incorrectProof.diagnostic!,
                    unlimitedTokensModelParams.multiroundProfile.proofFixPrompt
                ),
            },
        ]);
    });
});