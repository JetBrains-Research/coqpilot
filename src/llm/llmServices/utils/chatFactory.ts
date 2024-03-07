import * as assert from "assert";

import { Theorem } from "../../../coqParser/parsedTypes";
import { ProofGenerationContext } from "../../proofGenerationContext";
import { ChatHistory, ChatMessage } from "../chat";
import { ProofVersion } from "../llmService";
import { ModelParams } from "../modelParams";

import { ChatTokensFitter } from "./chatTokensFitter";
import {
    UserAssistantChatItem,
    chatItemToContent,
    itemizedChatToHistory,
} from "./chatUtils";

export function validateChat(chat: ChatHistory): [boolean, string] {
    if (chat.length < 1) {
        return [false, "no system message at the chat start"];
    }
    let prevRole = chat[0].role;
    if (prevRole !== "system") {
        return [false, "no system message at the chat start"];
    }
    for (const message of chat.slice(1)) {
        const curRole = message.role;
        if (curRole === "system") {
            return [false, "several system messages found"];
        }
        if (prevRole === curRole) {
            return [false, "two identical roles in a row"];
        }
        prevRole = curRole;
    }
    const lastMessageRole = chat[chat.length - 1].role;
    if (lastMessageRole === "assistant") {
        return [
            false,
            "last message in the chat should be authored either by `user` or by `system`",
        ];
    }
    return [true, "ok"];
}

export function buildChat(
    ...chats: (ChatHistory | ChatMessage)[]
): ChatHistory {
    const chat: ChatHistory = [];
    chat.concat(...chats);
    const [isValid, errorMessage] = validateChat(chat);
    assert.ok(isValid, errorMessage);
    return chat;
}

export function buildProofGenerationChat(
    proofGenerationContext: ProofGenerationContext,
    modelParams: ModelParams
): ChatHistory {
    const fitter = new ChatTokensFitter(
        modelParams.modelName,
        modelParams.newMessageMaxTokens!,
        modelParams.tokensLimit!
    );

    const systemMessage: ChatMessage = {
        role: "system",
        content: modelParams.systemPrompt!,
    };
    fitter.fitRequiredMessage(systemMessage);

    const completionTargetMessage: ChatMessage = {
        role: "user",
        content: proofGenerationContext.completionTarget,
    };
    fitter.fitRequiredMessage(completionTargetMessage);

    const fittedContextTheorems = fitter.fitOptionalObjects(
        proofGenerationContext.contextTheorems,
        (theorem) => chatItemToContent(theoremToChatItem(theorem))
    );
    const contextTheoremsChat = buildTheoremsChat(fittedContextTheorems);

    return buildChat(
        systemMessage,
        contextTheoremsChat,
        completionTargetMessage
    );
}

export function buildProofFixChat(
    proofGenerationContext: ProofGenerationContext,
    proofVersions: ProofVersion[],
    modelParams: ModelParams
): ChatHistory {
    const fitter = new ChatTokensFitter(
        modelParams.modelName,
        modelParams.newMessageMaxTokens!,
        modelParams.tokensLimit!
    );

    const systemMessage: ChatMessage = {
        role: "system",
        content: modelParams.systemPrompt!,
    };
    fitter.fitRequiredMessage(systemMessage);

    const completionTargetMessage: ChatMessage = {
        role: "user",
        content: proofGenerationContext.completionTarget,
    };
    const lastProofVersion = proofVersions[proofVersions.length - 1];
    const proofMessage: ChatMessage = {
        role: "assistant",
        content: lastProofVersion.proof,
    };
    const proofFixMessage: ChatMessage = {
        role: "user",
        content: createProofFixMessage(
            lastProofVersion.diagnostic!,
            modelParams.multiroundProfile.proofFixPrompt
        ),
    };
    fitter.fitRequiredMessage(completionTargetMessage);
    fitter.fitRequiredMessage(proofMessage);
    fitter.fitRequiredMessage(proofFixMessage);

    const fittedProofVersions = fitter.fitOptionalObjects(
        proofVersions.slice(0, proofVersions.length - 1),
        (proofVersion) =>
            chatItemToContent(proofVersionToChatItem(proofVersion))
    );
    const previousProofVersionsChat =
        buildPreviousProofVersionsChat(fittedProofVersions);

    const fittedContextTheorems = fitter.fitOptionalObjects(
        proofGenerationContext.contextTheorems,
        (theorem) => chatItemToContent(theoremToChatItem(theorem))
    );
    const contextTheoremsChat = buildTheoremsChat(fittedContextTheorems);

    return buildChat(
        systemMessage,
        contextTheoremsChat,
        completionTargetMessage,
        previousProofVersionsChat,
        proofMessage,
        proofFixMessage
    );
}

function createProofFixMessage(
    diagnostic: string,
    proofFixPrompt: string
): string {
    return proofFixPrompt.replace("${diagnostic}", diagnostic);
}

export function theoremToChatItem(theorem: Theorem): UserAssistantChatItem {
    return {
        userMessage: theorem.statement,
        assistantMessage: theorem.proof?.onlyText() ?? "Admitted.",
    };
}

export function buildTheoremsChat(theorems: Theorem[]): ChatHistory {
    return itemizedChatToHistory(theorems.map(theoremToChatItem));
}

export function proofVersionToChatItem(
    proofVersion: ProofVersion
): UserAssistantChatItem {
    return {
        userMessage: proofVersion.proof,
        assistantMessage: proofVersion.diagnostic!,
    };
}

export function buildPreviousProofVersionsChat(
    proofVersions: ProofVersion[]
): ChatHistory {
    return itemizedChatToHistory(proofVersions.map(proofVersionToChatItem));
}
