import { TiktokenModel, encoding_for_model } from "tiktoken";

export function calculateTokensViaTikToken(
    text: string,
    model: TiktokenModel
): number {
    const encoder = encoding_for_model(model);
    const tokens = encoder.encode(text).length;
    encoder.free();
    return tokens;
}

export function approxCalculateTokens(text: string): number {
    return (text.length / 4) >> 0;
}
