import { SimpleShowableError } from "../../../../utils/errors/simpleShowableError";

export class InstallationFailedError extends SimpleShowableError {
    constructor(errorMessage: string, messageToShow: string) {
        super(errorMessage, messageToShow);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "InstallationFailedError";
    }
}
