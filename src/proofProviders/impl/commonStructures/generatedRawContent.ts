import { GenerationTokens } from "./generationTokens";

export interface GeneratedRawContent {
    items: GeneratedRawContentItem[];
    /**
     * Tokens spent to generate all content in total.
     *
     * Although content items by themselves provide tokens metrics too,
     * their sum might not always be equal to the `tokensSpentInTotal` metrics:
     * - some optimization might occur (for example, same prompt for different generated responses
     *   might not consume extra tokens);
     * - sometimes, it is impossible to obtain item-specific tokens metrics,
     *   so they might be estimated approximately only.
     *
     * Therefore, **the most accurate number** of tokens spent for the generation
     * is provided by this `tokensSpentInTotal` property.
     * In contrast, per-item `tokensSpent` should be used mostly as an approximate estimation.
     */
    tokensSpentInTotal: GenerationTokens;
}

export interface GeneratedRawContentItem {
    content: string;
    /**
     * Tokens spent to generate this specific content item.
     *
     * **Warning:** most likely, these metrics might be just an approximate estimation of the real ones.
     * To get probably more accurate (but aggregated) data, use `GeneratedRawContent.tokensSpentInTotal` instead
     * (check its docs for more details).
     */
    tokensSpent: GenerationTokens;
}
