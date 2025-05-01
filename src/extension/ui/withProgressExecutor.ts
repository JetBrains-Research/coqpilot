import { ProgressLocation, window } from "vscode";

export async function executeWithProgress(
    title: string,
    block: () => Promise<void>
) {
    return window.withProgress(
        {
            location: ProgressLocation.Notification,
            title: title,
            cancellable: false,
        },
        async () => block()
    );
}
