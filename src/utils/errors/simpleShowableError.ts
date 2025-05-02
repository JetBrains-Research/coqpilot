export class SimpleShowableError extends Error {
    constructor(
        errorMessage: string,
        readonly messageToShow: string
    ) {
        super(errorMessage);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "SimpleShowableError";
    }
}
