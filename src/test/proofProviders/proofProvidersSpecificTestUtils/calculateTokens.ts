import { TiktokenModel } from "tiktoken";

import { TokensCounter } from "../../../proofProviders/impl/utils/chatTokensFitter";

export function calculateTokensViaTikToken(
    text: string,
    model: TiktokenModel
): number {
    return countTokens(text, model);
}

export function approxCalculateTokens(text: string): number {
    return countTokens(text, undefined);
}

function countTokens(text: string, model: TiktokenModel | undefined): number {
    const tokensCounter = new TokensCounter(model);
    try {
        return tokensCounter.countTokens(text);
    } finally {
        tokensCounter.dispose();
    }
}
