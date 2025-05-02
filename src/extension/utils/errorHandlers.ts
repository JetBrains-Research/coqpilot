import { buildErrorCompleteLog } from "../../utils/errors/errorsUtils";
import { SimpleShowableError } from "../../utils/errors/simpleShowableError";
import { SettingsValidationError } from "../settings/settingsValidationError";
import {
    EditorMessages,
    showMessageToUser,
} from "../ui/messages/editorMessages";

export function reportErrorToUser(e: any) {
    if (e instanceof SettingsValidationError) {
        e.showAsMessageToUser();
    } else if (e instanceof SimpleShowableError) {
        showMessageToUser(e.messageToShow, "error");
    } else {
        showMessageToUser(
            e instanceof Error
                ? EditorMessages.errorOccurred(e.message)
                : EditorMessages.objectWasThrownAsError(e),
            "error"
        );
        console.error(buildErrorCompleteLog(e));
    }
}
