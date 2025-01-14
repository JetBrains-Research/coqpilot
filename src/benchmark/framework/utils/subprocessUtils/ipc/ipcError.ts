import { ErrorWithCause } from "../../../../../utils/errorsUtils";

export class IPCError extends ErrorWithCause {
    constructor(message: string) {
        super(message);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "IPCError";
    }
}
