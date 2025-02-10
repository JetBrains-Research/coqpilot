import { buildErrorCompleteLog } from "./errorsUtils";

export function throwError(...message: string[]): never {
    throw Error(message.join(""));
}

export function illegalState(...message: string[]): never {
    throw new IllegalStateError(`Illegal state: ${message.join("")}`);
}

export function unexpectedError(err: any): never {
    throw new IllegalStateError(
        `unexpected error occurred:\n${buildErrorCompleteLog(err)}`
    );
}

export function invariantFailed(
    invariantName: string,
    ...message: string[]
): never {
    throw new InvariantFailedError(
        `${invariantName} invariant failed: ${message.join("")}`
    );
}

export function unreachable(...message: string[]): never {
    throw new UnreachableCodeReachedError(
        `Unreachable code reached: ${message.join("")}`
    );
}

export function unsupported(...message: string[]): never {
    throw new UnsupportedError(message.join(""));
}

export class IllegalStateError extends Error {
    constructor(message: string) {
        super(message);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "IllegalStateError";
    }
}

export class InvariantFailedError extends IllegalStateError {
    constructor(message: string) {
        super(message);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "InvariantFailedError";
    }
}

export class UnreachableCodeReachedError extends IllegalStateError {
    constructor(message: string) {
        super(message);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "UnreachableCodeReachedError";
    }
}

export class UnsupportedError extends Error {
    constructor(message: string) {
        super(message);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "UnsupportedError";
    }
}
