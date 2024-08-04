import { JSONSchemaType } from "ajv";

export interface LengthMetrics {
    inSteps?: number;
    inSymbols?: number;
    inTokens?: number;
}

export interface EstimatedChatTokens {
    requestChatTokens: number;
    responseMessageTokens: number;
    tokensInTotal: number;
}

export interface CodeElementRangeInterface {
    start: CodeElementPositionInterface;
    end: CodeElementPositionInterface;
}

export class CodeElementRange implements CodeElementRangeInterface {
    constructor(
        readonly start: CodeElementPosition,
        readonly end: CodeElementPosition
    ) {}

    toString(): string {
        return `(${this.start}):(${this.end})`;
    }

    equalsTo(other: CodeElementRange): boolean {
        return this.start.equalsTo(other.start) && this.end.equalsTo(other.end);
    }
}

export function fromRange(range: CodeElementRangeInterface): CodeElementRange {
    return new CodeElementRange(
        fromPosition(range.start),
        fromPosition(range.end)
    );
}

export interface CodeElementPositionInterface {
    line: number;
    character: number;
}

export class CodeElementPosition implements CodeElementPositionInterface {
    constructor(
        readonly line: number,
        readonly character: number
    ) {}

    toString(): string {
        return `${this.line}:${this.character}`;
    }

    equalsTo(other: CodeElementPosition): boolean {
        return this.line === other.line && this.character === other.character;
    }
}

export function fromPosition(
    position: CodeElementPositionInterface
): CodeElementPosition {
    return new CodeElementPosition(position.line, position.character);
}

export interface SerializedCodeElementRange {
    start: SerializedCodeElementPosition;
    end: SerializedCodeElementPosition;
}

export interface SerializedCodeElementPosition {
    line: number;
    character: number;
}

export const serializedCodeElementPositionSchema: JSONSchemaType<SerializedCodeElementPosition> =
    {
        type: "object",
        properties: {
            line: {
                type: "number",
            },
            character: {
                type: "number",
            },
        },
        required: ["line", "character"],
        additionalProperties: false,
    };

export const serializedCodeElementRangeSchema: JSONSchemaType<SerializedCodeElementRange> =
    {
        type: "object",
        properties: {
            start: serializedCodeElementPositionSchema,
            end: serializedCodeElementPositionSchema,
        },
        required: ["start", "end"],
        additionalProperties: false,
    };

export function deserializeCodeElementRange(
    serializedCodeElementRange: SerializedCodeElementRange
): CodeElementRange {
    return new CodeElementRange(
        deserializeCodeElementPosition(serializedCodeElementRange.start),
        deserializeCodeElementPosition(serializedCodeElementRange.end)
    );
}

export function serializeCodeElementRange(
    codeElementRange: CodeElementRangeInterface
): SerializedCodeElementRange {
    return {
        start: serializeCodeElementPosition(codeElementRange.start),
        end: serializeCodeElementPosition(codeElementRange.end),
    };
}

export function deserializeCodeElementPosition(
    serializedCodeElementPosition: SerializedCodeElementPosition
): CodeElementPosition {
    return new CodeElementPosition(
        serializedCodeElementPosition.line,
        serializedCodeElementPosition.character
    );
}

export function serializeCodeElementPosition(
    codeElementPosition: CodeElementPositionInterface
): SerializedCodeElementPosition {
    return {
        line: codeElementPosition.line,
        character: codeElementPosition.character,
    };
}
