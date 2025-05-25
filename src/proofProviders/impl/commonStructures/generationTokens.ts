export interface GenerationTokens {
    promptTokens: number;
    /**
     * All tokens generated in response to the prompt sent.
     * If the content is somehow parsed out the generated response,
     * `generatedTokens` might count more tokens than the content solely takes.
     */
    generatedTokens: number;
    tokensSpentInTotal: number;
}

export function constructGenerationTokens(
    promptTokens: number,
    generatedTokens: number
): GenerationTokens {
    return {
        promptTokens: promptTokens,
        generatedTokens: generatedTokens,
        tokensSpentInTotal: promptTokens + generatedTokens,
    };
}

export function zeroTokens(): GenerationTokens {
    return {
        promptTokens: 0,
        generatedTokens: 0,
        tokensSpentInTotal: 0,
    };
}
/**
 * Adds metrics from `from` to `to` and returns the modified `to` structure.
 */
function addGenerationTokens(
    to: GenerationTokens,
    from: GenerationTokens
): GenerationTokens {
    to.promptTokens += from.promptTokens;
    to.generatedTokens += from.generatedTokens;
    to.tokensSpentInTotal += from.tokensSpentInTotal;
    return to;
}

export function sumGenerationTokens(
    generationTokensList: GenerationTokens[]
): GenerationTokens {
    return generationTokensList.reduce(
        (acc, generationTokens) => addGenerationTokens(acc, generationTokens),
        zeroTokens()
    );
}
