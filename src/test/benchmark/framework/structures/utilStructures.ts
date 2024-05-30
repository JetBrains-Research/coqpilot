import { Theorem } from "../../../../coqParser/parsedTypes";

export class TheoremData {
    constructor(readonly theorem: Theorem) {}

    readonly name = this.theorem.name;
    readonly proof = this.theorem.proof;

    // TODO: count length accurately
    // readonly proofLength: LengthMetrics = {
    //     inSteps: this.theorem.proof?.proof_steps.length ?? 0,
    // };
}

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

export class CodeElementRange {
    constructor(
        readonly start: CodeElementPosition,
        readonly end: CodeElementPosition
    ) {}

    toString(): string {
        return `(${this.start}):(${this.end})`;
    }
}

export class CodeElementPosition {
    constructor(
        readonly line: number,
        readonly character: number
    ) {}

    toString(): string {
        return `${this.line}:${this.character}`;
    }

    // TODO: build from vscode Position
}
