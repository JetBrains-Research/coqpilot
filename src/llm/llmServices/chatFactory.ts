import { Theorem } from "../../coqParser/parsedTypes";
import {
    ChatHistory,
    chatItemToContent,
    ChatMessage,
    itemizedChatToHistory,
    UserAssistantChatItem,
} from "./chat";
import { ProofGenerationContext, ProofVersion } from "./llmService";
import * as assert from "assert";
import { ModelParams } from "./modelParams";
import { ChatTokensFitter } from "./chatTokensFitter";

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
        assistantMessage: proofVersion.diagnostic!, // TODO: handle undefined properly
    };
}

export function buildPreviousProofVersionsChat(
    proofVersions: ProofVersion[]
): ChatHistory {
    return itemizedChatToHistory(proofVersions.map(proofVersionToChatItem));
}

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

// TODO: support experiments
function createFixProofMessage(diagnostic: string): string {
    return `Unfortunately, the last proof is not correct. Here is the compiler's feedback: '${diagnostic}'. Please, fix the proof.`;
}

export function buildGenerateProofChat(
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
        content: modelParams.systemPromt!,
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

export function buildFixProofChat(
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
        content: modelParams.systemPromt!,
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
    const fixProofMessage: ChatMessage = {
        role: "user",
        content: createFixProofMessage(lastProofVersion.diagnostic!), // TODO: handle undefined properly
    };
    fitter.fitRequiredMessage(completionTargetMessage);
    fitter.fitRequiredMessage(proofMessage);
    fitter.fitRequiredMessage(fixProofMessage);

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
        fixProofMessage
    );
}
