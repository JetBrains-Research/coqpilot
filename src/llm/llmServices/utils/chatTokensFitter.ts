import { Tiktoken, TiktokenModel, encoding_for_model } from "tiktoken";

import { ChatMessage } from "../chat";

export class ChatTokensFitter {
    readonly tokensLimit: number;

    private tokens: number = 0;
    private readonly countTokens: (text: string) => number;

    constructor(
        modelName: string,
        newMessageMaxTokens: number,
        tokensLimit: number
    ) {
        this.tokensLimit = tokensLimit;
        if (this.tokensLimit < newMessageMaxTokens) {
            throw Error(
                `tokens limit ${this.tokensLimit} is not enough to generate a new message that needs up to ${newMessageMaxTokens}`
            );
        }
        this.tokens += newMessageMaxTokens;

        let encoder: Tiktoken | undefined = undefined;
        try {
            encoder = encoding_for_model(modelName as TiktokenModel);
        } catch (e) {}
        this.countTokens = (text: string) => {
            if (encoder) {
                return encoder.encode(text).length;
            } else {
                return (text.length / 4) >> 0;
            }
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
            throw Error(
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
            (sum, content) => sum + this.countTokens(content),
            0
        );
    }
}
