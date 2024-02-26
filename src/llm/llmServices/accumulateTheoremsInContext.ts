import { ProofGenerationContext } from "./modelParamsInterfaces";
import { Theorem } from "../../coqParser/parsedTypes";
import { encoding_for_model, Tiktoken, TiktokenModel } from "tiktoken";

export function pickTheoremsUntilTokenLimit(
    answerMaxTokens: number,
    proofGenerationContext: ProofGenerationContext,
    systemMessage: string,
    model: string,
    // Input length + generated tokens max length.
    modelContextWindowTokens: number
): Theorem[] {
    let encoder: Tiktoken | undefined = undefined;
    try {
        encoder = encoding_for_model(model as TiktokenModel);
    } catch (e) {}

    const countTokes = (text: string) => {
        if (encoder) {
            return calculateTokens(text, encoder);
        } else {
            return approxCalculateTokens(text);
        }
    };

    const contextTheorems: Theorem[] = [];
    const targetMessageTokens = countTokes(
        proofGenerationContext.admitCompletionTarget
    );
    let tokenCount =
        countTokes(systemMessage) + targetMessageTokens + answerMaxTokens;

    for (const theorem of proofGenerationContext.sameFileTheorems) {
        const statementTokens = countTokes(theorem.statement);
        const theoremProof = theorem.proof?.onlyText() ?? "";
        const proofTokens = countTokes(theoremProof);

        if (
            tokenCount + statementTokens + proofTokens >
            modelContextWindowTokens
        ) {
            break;
        }

        contextTheorems.push(theorem);
        tokenCount += statementTokens + proofTokens;
    }

    encoder?.free();

    return contextTheorems;
}

function calculateTokens(text: string, encoder: Tiktoken): number {
    return encoder.encode(text).length;
}

function approxCalculateTokens(text: string): number {
    return (text.length / 4) >> 0;
}
