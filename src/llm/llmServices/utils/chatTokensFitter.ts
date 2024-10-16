import { Tiktoken, TiktokenModel, encoding_for_model } from "tiktoken";

import { ConfigurationError } from "../../llmServiceErrors";
import { ChatMessage, EstimatedTokens } from "../commonStructures/chat";

export class ChatTokensFitter {
    readonly tokensLimit: number;

    private tokens: number = 0;
    private tokensCounter: TokensCounter;

    constructor(
        private readonly maxTokensToGenerate: number,
        tokensLimit: number,
        modelName?: string
    ) {
        this.tokensLimit = tokensLimit;
        if (this.tokensLimit < this.maxTokensToGenerate) {
            throw new ConfigurationError(
                `tokens limit ${this.tokensLimit} is not enough for the model to generate a new message that needs up to ${maxTokensToGenerate}`
            );
        }
        this.tokens += this.maxTokensToGenerate;

        this.tokensCounter = new TokensCounter(modelName);
    }

    dispose() {
        this.tokensCounter.dispose();
    }

    estimateTokens(): EstimatedTokens {
        return {
            messagesTokens: this.tokens - this.maxTokensToGenerate,
            maxTokensToGenerate: this.maxTokensToGenerate,
            maxTokensInTotal: this.tokens,
        };
    }

    fitRequiredMessage(message: ChatMessage) {
        this.fitRequired(message.content);
    }

    fitOptionalMessage(message: ChatMessage): boolean {
        return this.fitOptional(message.content);
    }

    fitOptionalObjects<Type>(
        objects: Type[],
        extractContent: (object: Type) => string[]
    ): Type[] {
        let fittedObjects: Type[] = [];
        for (const object of objects) {
            if (!this.fitOptional(...extractContent(object))) {
                break;
            }
            fittedObjects.push(object);
        }
        return fittedObjects;
    }

    private fitRequired(...contents: string[]) {
        const contentTokens = this.countContentTokens(...contents);
        if (this.tokens + contentTokens > this.tokensLimit) {
            throw new ConfigurationError(
                `required content cannot be fitted into tokens limit: '${contents}' require ${contentTokens} + previous ${this.tokens} tokens > max ${this.tokensLimit}`
            );
        }
        this.tokens += contentTokens;
    }

    private fitOptional(...contents: string[]): boolean {
        const contentTokens = this.countContentTokens(...contents);
        if (this.tokens + contentTokens <= this.tokensLimit) {
            this.tokens += contentTokens;
            return true;
        }
        return false;
    }

    private countContentTokens(...contents: string[]): number {
        return contents.reduce(
            (sum, content) => sum + this.tokensCounter.countTokens(content),
            0
        );
    }
}

export class TokensCounter {
    private encoder: Tiktoken | undefined;
    private readonly countTokensInternal: (text: string) => number;

    constructor(modelName: string | undefined) {
        this.encoder = undefined;
        try {
            this.encoder = encoding_for_model(modelName as TiktokenModel);
        } catch (e) {}
        this.countTokensInternal = (text: string) => {
            if (this.encoder) {
                return this.encoder.encode(text).length;
            } else {
                return Math.floor(text.length / 4);
            }
        };
    }

    countTokens(text: string): number {
        return this.countTokensInternal(text);
    }

    dispose() {
        this.encoder?.free();
    }
}
