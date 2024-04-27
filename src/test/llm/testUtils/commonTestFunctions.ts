import { TiktokenModel, encoding_for_model } from "tiktoken";
import * as tmp from "tmp";

import { MockLLMService } from "./mockLLMService";

export const gptTurboModel = "gpt-3.5-turbo-0301";

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

export function createMockLLMService(): MockLLMService {
    return new MockLLMService(tmp.fileSync().name);
}
