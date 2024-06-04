export abstract class ExecutionResult<T> {
    constructor(readonly maybeResult: T | undefined) {}

    isSuccessful(): this is SuccessfullExecution<T> {
        return this instanceof SuccessfullExecution;
    }

    isFailed(): this is FailedExecution<T> {
        return this instanceof FailedExecution;
    }
}

export class SuccessfullExecution<T> extends ExecutionResult<T> {
    constructor(readonly result: T) {
        super(result);
    }
}

export class FailedExecution<T> extends ExecutionResult<T> {
    constructor(
        readonly errorTypeName: string | undefined,
        readonly errorMessage: string
    ) {
        super(undefined);
    }
}
