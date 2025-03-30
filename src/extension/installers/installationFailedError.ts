import { showMessageToUser } from "../ui/messages/editorMessages";

export class InstallationFailedError extends Error {
    constructor(
        errorMessage: string,
        private readonly messageToShowToUser: string
    ) {
        super(errorMessage);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "InstallationFailedError";
    }

    showAsMessageToUser() {
        showMessageToUser(this.messageToShowToUser, "error");
    }
}
